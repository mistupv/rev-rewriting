# Reversible Term Rewriting

A tool written in Prolog for the transformation of an irreversible Term Rewriting System into a reversible one.

### Dependencies

This tool uses the [tokenize library](https://github.com/aBathologist/tokenize).
You can install it from SWI-Prolog with the command:
```
?- pack_install(tokenize).
```

### How to use

First, load the rules from the *rev.pl* script as usual:
```
?- [rev].
```
Then, call the main rule (`fscd/1`) with the path to your .trs file (an atom).

For instance, to use the example TRS [AProVE webpage](http://aprove.informatik.rwth-aachen.de/help_new/trs.html#trs):
```
?- fscd('examples/aprove.trs').
```
The program will start its execution and print the transformed systems at each step.

### Publications

This tool is an implementation of the proposed transformations in the following publications:
  * Naoki Nishida, Adrián Palacios and Germán Vidal. [Reversible Term Rewriting](http://drops.dagstuhl.de/opus/volltexte/`2016/5984/). *Proceedings of the First International Conference on Formal Structures for Computation and Deduction*, 2016, pages 28:1-28:18.

### Others

Check [this video](https://www.youtube.com/watch?v=f9GHNtbupxM) for the talk about this topic.
