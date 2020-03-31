use hopscotch::Queue;
use std::io;

fn main() {
    let mut count = 0;
    let mut buffer: Queue<usize> = Queue::with_capacity(5);
    loop {
        let mut input = String::new();
        match io::stdin().read_line(&mut input) {
            Ok(_) => match input.trim().split(' ').collect::<Vec<_>>().as_slice() {
                ["push", k] => {
                    let tag = k.trim().parse().unwrap();
                    let i = buffer.push(tag, count);
                    println!("{}", buffer);
                    println!("Result: {:?}", i);
                    count += 1;
                }
                ["push_and_pop", k] => {
                    let tag = k.trim().parse().unwrap();
                    let i = buffer.push_and_pop(tag, count, false);
                    println!("{}", buffer);
                    println!("Result: {:?}", i);
                    count += 1;
                }
                ["pop"] => {
                    let r = buffer.pop();
                    println!("{}", buffer);
                    println!("Result: {:?}", r);
                }
                ["get_after", i, ks @ ..] => {
                    let tags: Vec<usize> = ks.iter().map(|k| k.trim().parse().unwrap()).collect();
                    let r = buffer.get_after(i.trim().parse().unwrap(), &tags);
                    println!("Result: {:?}", &r);
                }
                l => println!("Unrecognized command: {:?}", l),
            },
            Err(err) => eprintln!("error: {}", err),
        }
    }
}
