use hopscotch::Queue;
use std::io;

fn main() {
    let mut count = 0;
    let mut buffer: Queue<usize, usize> = Queue::with_capacity(5);
    loop {
        print!("> ");
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
                l => println!("Unrecognized command: {:?}", l),
            },
            Err(err) => eprintln!("error: {}", err),
        }
    }
}
