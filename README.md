# tla-specs

Collection of specifications exploring several applications of [TLA+](https://lamport.azurewebsites.net/tla/tla.html). Mostly with documentation explaining the reasoning.

* [crdt-bug](https://github.com/Alexander-N/tla-specs/tree/main/crdt-bug) - Shows a subtle problem in a CRDT algorithm posted by Martin Kleppmann on twitter. Also contains a specification of a fixed version.
* [aiorwlock](https://github.com/Alexander-N/tla-specs/tree/main/aiorwlock) - Based on this [talk](https://www.youtube.com/watch?v=gRr9ymtAN6E) I only slightly changed an existing specification from a Python library and added a second one for a bug that existed at one point.
* [asyncio-lock](https://github.com/Alexander-N/tla-specs/tree/main/asyncio-lock) - Same idea as above, models several bugs that have been present at some point in Python's [asyncio
lock](https://docs.python.org/3/library/asyncio-sync.html#lock).
* [dual-writes](https://github.com/Alexander-N/tla-specs/tree/main/dual-writes) - Takes a simple race condition to explore ways to create visualizations of the problem.
* [paxos-from-the-ground-up](https://github.com/Alexander-N/tla-specs/tree/main/paxos-from-the-ground-up) - WIP: Idea is to create one spec for each step in a [tutorial](http://imnaseer.net/paxos-from-the-ground-up.html) which builds up paxos by refining a simple but wrong protocol step by step.
* [tic-tac-toe](https://github.com/Alexander-N/tla-specs/tree/main/tic-tac-toe) - Models a game of tic-tac-toe of two players with different strategies. Contains ideas from [other](https://pron.github.io/files/TicTacToe.pdf) [specs](https://groups.google.com/g/tlaplus/c/rSmABu1YTw4/m/SrICRC12AAAJ).
* [tower-of-hanoi](https://github.com/Alexander-N/tla-specs/tree/main/tower-of-hanoi) - A simple, heavily commented specification of a classic puzzle.
