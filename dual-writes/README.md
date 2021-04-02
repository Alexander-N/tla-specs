# Dual Writes

Demonstrates a race condition described in https://martin.kleppmann.com/2015/05/27/logs-for-data-infrastructure.html, image from Martin Kleppmanns talk:

<img src="images/logs-11.png" width="70%">

While [dual_writes.tla](dual_writes.tla) is enough to model the problem, there is also [dual_writes_shiviz.tla](dual_writes_shiviz.tla) which uses the [ShiViz TLA+ community module](https://github.com/tlaplus/CommunityModules/blob/master/modules/ShiViz.tla) as described in this [issue](https://github.com/tlaplus/tlaplus/issues/267#issuecomment-481951259) to produce an error trace which can be used as input to [ShiViz](https://bestchai.bitbucket.io/shiviz/).

Unfortunately this orders the events as they appear in the error trace, which does not need to reflect the causal relationships in the system.

For example we can get the following visualization:
![good trace](images/good_trace.png)

That seems sensible, but several pairs of events on ClientA and ClientB are connected by a line while in the system we model the clients don't communicate.

We can also get a trace like this, which might confuse more than it helps:
![bad trace](images/bad_trace.png)

TODO: Try to implement vector clocks in the spec to produce more accurate visualizations.
