use hopscotch::Queue;
use std::io::{self, Write};

fn main() {
    let mut count = 0;
    let mut buffer: Queue<usize, usize> = Queue::new();
    println!("Debug REPL for hopscotch::Queue<usize, usize>");
    println!("Available commands:\n  \
                • push <usize>\n  \
                • pop\n  \
                • after <u64> [<usize> ...]\n  \
                • before <u64> [<usize> ...]\n  \
                • exit");
    loop {
        print!("> ");
        io::stdout().flush();
        let mut input = String::new();
        match io::stdin().read_line(&mut input) {
            Ok(_) => match input.trim().split(' ').collect::<Vec<_>>().as_slice() {
                ["push", k] => {
                    let tag = k.trim().parse().unwrap();
                    let i = buffer.push(tag, count);
                    println!("Result: {:?}", i);
                    count += 1;
                }
                ["pop"] => {
                    let r = buffer.pop();
                    println!("Result: {:?}", r);
                }
                ["after", i, ks @ ..] => {
                    let tags: Vec<usize> = ks.iter().map(|k| k.trim().parse().unwrap()).collect();
                    let r = buffer.after(i.trim().parse().unwrap(), &tags);
                    println!("Result: {:?}", &r);
                }
                ["before", i, ks @ ..] => {
                    let tags: Vec<usize> = ks.iter().map(|k| k.trim().parse().unwrap()).collect();
                    let r = buffer.before(i.trim().parse().unwrap(), &tags);
                    println!("Result: {:?}", &r);
                }
                [""] | ["exit"] | ["quit"] => break,
                l => println!("Unrecognized command: {:?}", l),
            },
            Err(err) => eprintln!("error: {}", err),
        }
    }
}
