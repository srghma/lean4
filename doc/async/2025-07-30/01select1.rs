use tokio::sync::mpsc;
use tokio::select;

#[tokio::main]
async fn main() {
    let (tx1, mut rx1) = mpsc::channel(10);
    let (tx2, mut rx2) = mpsc::channel(10);

    tokio::spawn(async move {
        tx1.send(1).await.unwrap();
        tx1.send(2).await.unwrap();
    });
    tokio::spawn(async move {
        tx2.send(100).await.unwrap();
        tx2.send(200).await.unwrap();
    });

    loop {
        select! {
            Some(v) = rx1.recv() => {
                println!("rx1 got {}", v);
            }
            Some(v) = rx2.recv() => {
                println!("rx2 got {}", v);
            }
            else => break, // all closed
        }
    }
}
