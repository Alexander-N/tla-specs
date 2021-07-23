# Paxos from the ground up

[Paxos from the ground up](http://imnaseer.net/paxos-from-the-ground-up.html) is
a tutorial which derives the [Paxos consensus
algorithm](https://en.wikipedia.org/wiki/Paxos_(computer_science)) by starting
with a simple but wrong protocol and refining it step by step.

The idea here is to write one TLA+ spec for each step in the tutorial, which
exposes the defect in the incorrect protocol. I'll try to keep message passing
separate and general so that it can be reused for other specs, current state is
in [messaging.tla](messaging.tla).
