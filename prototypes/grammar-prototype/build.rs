fn main() {
    // pulls in .lalrpop files and builds them
    lalrpop::process_root().unwrap();
}
