use hopscotch::{self, ArcK};
use rust_embed::RustEmbed;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;
use tokio;
use tokio::sync::oneshot::{self, Sender};
use tokio::sync::{Mutex, RwLock};
use tokio::time;
use tokio::join;
use std::time::Duration;
use uuid::Uuid;
use std::hash::Hash;
use rand::Rng;

#[tokio::main]
async fn main() {
    let words = Arc::new(load_words());
    let events: Arc<Events<String, String>> =
        Arc::new(Events::with_capacity(100));

    // 100 times a second, a new word is added to the buffer, tagged with its
    // category.
    let push_words = words.clone();
    let push_events = events.clone();
    let f = tokio::spawn(async move {
        let mut interval = time::interval(Duration::from_millis(10));
        loop {
            let (category, word) = random_key_val(&push_words);
            push_events.push(category.clone(), word.clone()).await;
            interval.tick().await;
        }
    });

    // A listener looking for three different categories of word polls the event
    // buffer to see whether a new one is available, then "processes it" (delays
    // for some time), and then tries again.
    let g = tokio::spawn(async move {
        let categories = vec![
            random_key(&words),
            random_key(&words),
            random_key(&words),
        ];
        println!("Looking for: {:?}\n", categories);
        let mut index = 0;
        let tags = categories.into_iter();
        loop {
            let (event_index, category, word) =
                events.after(index, tags.clone()).await;
            println!("{}: {}", category, word);
            index = event_index + 1;
            tokio::time::delay_for(Duration::from_millis(350)).await;
        }
    });

    let (_, _) = join!(f, g);
}

/// A fixed-size event buffer with events of type `V` tagged with tags of type
/// `K`. Events are numbered sequentially as `u64`.
pub struct Events<K: Ord + Clone, V> {
    capacity: usize,
    buffer: RwLock<hopscotch::Queue<K, Arc<V>, ArcK>>,
    waiting: Mutex<Waiting<K, V>>,
}

/// A set of handles to tasks waiting for an event to occur.
struct Waiting<K: Ord + Clone, V> {
    waiting_ids: BTreeMap<K, HashSet<Uuid>>,
    id_sender: HashMap<Uuid, Sender<(u64, K, Arc<V>)>>,
}

impl<K: Ord + Clone, V> Events<K, V> {
    /// Create a new fixed-capacity buffer.
    pub fn with_capacity(capacity: usize) -> Events<K, V> {
        Events {
            capacity,
            buffer: RwLock::new(hopscotch::Queue::with_capacity(capacity)),
            waiting: Mutex::new(Waiting {
                waiting_ids: BTreeMap::new(),
                id_sender: HashMap::new(),
            }),
        }
    }

    /// Push a new event into the buffer.
    pub async fn push(&self, tag: K, value: V) {
        let value = Arc::new(value);
        let mut buffer = self.buffer.write().await;
        let mut waiting = self.waiting.lock().await;
        if let Some(ids) = waiting.waiting_ids.remove(&tag) {
            let index = buffer.next_index();
            for id in ids {
                waiting
                    .id_sender
                    .remove(&id)
                    .map(|sender| sender.send((index, tag.clone(), value.clone())))
                    .unwrap_or(Ok(())).unwrap_or(());
            }
        }
        buffer.push(tag, value);
        if buffer.len() > self.capacity {
            buffer.pop();
        }
    }

    /// Wait for an event after or including the given index, tagged with any of
    /// the given tags, and when it occurs, return its index, tag, and a
    /// reference to its data.
    pub async fn after<'a, Tags>(&self, index: u64, tags: Tags) -> (u64, K, Arc<V>)
    where
        Tags: IntoIterator<Item = &'a K>,
        Tags::IntoIter: Clone,
        K: 'a,
    {
        let buffer = self.buffer.read().await;
        let tags = tags.into_iter();
        if let Some(item) = buffer.after(index, tags.clone()) {
            eprint!("[buffered] ");
            if let Some(earliest) = buffer.earliest() {
                if index < earliest.index() {
                    eprint!("[lagged] ");
                }
            }
            (item.index(), item.tag().clone(), item.value().clone())
        } else {
            let mut waiting = self.waiting.lock().await;
            let id = Uuid::new_v4();
            for tag in tags {
                waiting
                    .waiting_ids
                    .entry(tag.clone())
                    .or_insert_with(HashSet::new)
                    .insert(id);
            }
            let (sender, receiver) = oneshot::channel();
            waiting.id_sender.insert(id, sender);
            drop(waiting);
            drop(buffer);
            receiver
                .await
                .expect("sender will not be dropped before dispatch")
        }
    }
}

// We embed and use the words from the curated categorized word lists found at:
// https://github.com/imsky/wordlists

#[derive(RustEmbed)]
#[folder = "examples/wordlists/nouns"]
struct Nouns;

#[derive(RustEmbed)]
#[folder = "examples/wordlists/verbs"]
struct Verbs;

#[derive(RustEmbed)]
#[folder = "examples/wordlists/adjectives"]
struct Adjectives;

fn lines_iter<Asset: RustEmbed>() -> impl Iterator<Item = (String, Vec<String>)> {
    Asset::iter().map(|filename| {
        let contents = Asset::get(&filename).unwrap();
        (
            filename.replace(".txt", ""),
            std::str::from_utf8(&contents)
                .unwrap()
                .split('\n')
                .map(String::from)
                .filter(|s| !s.is_empty())
                .collect::<Vec<_>>(),
        )
    })
}

fn load_words() -> HashMap<String, Vec<String>> {
    let mut map = HashMap::new();
    map.extend(lines_iter::<Nouns>());
    map.extend(lines_iter::<Verbs>());
    map.extend(lines_iter::<Adjectives>());
    map
}

fn random_key<K: Hash + Eq, V>(map: &HashMap<K, Vec<V>>) -> &K {
    let mut rng = rand::thread_rng();
    let key_number = rng.gen::<usize>() % map.len();
    map.keys().nth(key_number).unwrap()
}

fn random_key_val<K: Hash + Eq, V>(map: &HashMap<K, Vec<V>>) -> (&K, &V) {
    let mut rng = rand::thread_rng();
    let key = random_key(map);
    let values = map.get(key).unwrap();
    let val = &values[rng.gen::<usize>() % values.len()];
    (key, val)
}
