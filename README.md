# tla-specs

Exploring applications of [TLA+](https://en.wikipedia.org/wiki/TLA%2B).

* [crdt-bug](crdt-bug) - A subtle problem and it's solution in a CRDT algorithm posted by Martin Kleppmann on Twitter.
* [aiorwlock](aiorwlock) - Based on this [talk](https://www.youtube.com/watch?v=gRr9ymtAN6E), models a bug that existed at one point in [aiorwlock](https://github.com/aio-libs/aiorwlock).
* [asyncio-lock](asyncio-lock) - Same idea as in [aiorwlock](aiorwlock) models several bugs that have been present at some point in Python's [standard library](https://docs.python.org/3/library/asyncio-sync.html#lock).
* [dual-writes](dual-writes) - Explores ways to create visualizations of a simple race condition.
* [paxos-from-the-ground-up](paxos-from-the-ground-up) - WIP: Idea is to create one spec for each step in a [tutorial](http://imnaseer.net/paxos-from-the-ground-up.html) which builds up paxos by refining a simple but wrong protocol step by step.
* [tic-tac-toe](tic-tac-toe) - A game of tic-tac-toe of two players with different strategies. Contains ideas from [other](https://pron.github.io/files/TicTacToe.pdf) [specs](https://groups.google.com/g/tlaplus/c/rSmABu1YTw4/m/SrICRC12AAAJ).
* [tower-of-hanoi](tower-of-hanoi) - Simple, heavily commented specification of a classic puzzle.
* [rate-limiter](rate-limiter) - Race condition described in the [redis documentation](https://redis.io/commands/incr/#pattern-rate-limiter-2).
