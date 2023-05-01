# Constructor-based Interactive Theorem Prover (CITP)

CITP is a tool for proving properties of software systems specified using a form of order-sorted algebra with transition rules. 
In other words, the models are oriented graphs or transition systems endowed with an order-sorted algebraic structure. 
Moreover, some of the operations used, namely those that are regarded as constructors – and which are used to ‘build’ states – need to be monotonic, meaning that they preserve the transitions.

## Obtaining CITP

CITP uses [Maude 3](http://maude.cs.illinois.edu/w/index.php?title=The_Maude_System)
as a rewriting engine. Hence, the first step is to download and
install the Maude system following the instructions available
[here](http://maude.cs.illinois.edu/w/index.php?title=Maude_download_and_installation).

Once Maude has been installed, you can download the latest (May 2023) distribution
of CITP from [here](https://github.com/ittutu/CITP/raw/master/Tool/dist/citp-23.05.tar.gz).

### System-wide installation

On GNU/Linux or macOS machines, the simplest way to install CITP is by
running the following scripts from the directory where the latest CITP
distribution has been downloaded (as a `tar.gz` archive):

```shell
tar -xzf citp-*.*.tar.gz
cd citp-*.*
./configure
make
sudo make install
```

### Explicit loading into Maude

Alternatively, you could also copy the CITP files to a destination of
your choosing, and then explicitly load them into Maude whenever you
decide to run the tool. For example:

```shell
tar -xzf citp-*.*.tar.gz
cp -R citp-*.*/src/ /home/user/citp
```

In this case, you need to set the `MAUDE_LIB` environment variable
appropriately, making sure it includes paths to libraries that are
bundled with Maude and to the CITP installation directory.  For
example, assuming that Maude in installed under `/usr/local/maude`,
you could execute:

```shell
export MAUDE_LIB=/usr/local/maude:/home/user/citp
```

To make this setting persistent, you could add the above line to your
`.bashrc` file.

## Executing CITP

If you opted for a system-wide installation, then CITP can be launched
from the command line by typing:

```shell
citp [files]
```

where `[files]` is a list of Maude files that you would like to have
loaded into Maude (in order to prove properties of them) before CITP.

If you decided to load CITP explicitly into Maude, then you could
launch the tool by typing:

```shell
maude -no-banner -allow-files [files] run-citp
```

### Using CITP

Once CITP has started, you can load external proof files using the
command `load file`, exit the tool using the command `quit`, or input
goals and proofs directly from the command line.

To give an example, suppose we would like to prove that the
multiplication of natural numbers distributes over addition.
The first step is define the goal that we would like to prove.
In our case, we prove the distributivity property based on two
premises, which correspond to a standard axiomatization of the
multiplication of natural numbers.

```
goal DIST is
  fm forall {Y:Nat} 0 * Y:Nat = 0 .
  fm forall {X:Nat, Y:Nat} (s X:Nat) * Y:Nat = X:Nat * Y:Nat + Y:Nat .
|-{NAT}
  fm forall {X:Nat, Y:Nat, Z:Nat} X:Nat * (Y:Nat + Z:Nat) = X:Nat * Y:Nat + X:Nat * Z:Nat .
endg
```

The proof is done in three steps, each captured by a CITP tactic.
First, we apply induction on the variable `X`, which generates two new
(simpler) goals; then, we push all executable premises (including the
induction hypothesis) so that they could be used for term reductions
in the rest of the proof; and finally, we apply the tactic `red`,
which discharges all remaining goals.

```
begin proof P of DIST
  ind(X:Nat)
  push-all
  red
qed
```

Several more complex examples are available [here](https://github.com/ittutu/CITP/tree/master/Examples).

## Commands

### System-level commands

CITP supports the following system-level commands:
- `load F` reads the contents of a file named `F`; both relative and absolute paths are accepted.
- `eof` causes the tool to stop reading from the current file.
- `quit` or `q` terminates the execution of the tool.
- `list goals` lists the names of all goals loaded into the CITP database.
- `show goal G` displays the definition of a goal named `G`.
- `list proofs` lists the names of all proofs loaded into the CITP database.
- `show proof P` displays tactics used within the proof `P`.
- `begin proof P of G` starts a new proof, named `P` of the goal `G`.

### Proof commands

Within proofs, i.e., after executing a `begin proof` command, CITP supports a different set of commands:
- `show proof` displays the tactics used so far in the proof.
- `show goals [abridged]` displays summaries of all open goals.
- `show goal [abridged]` displays a summary of the curent open goal.
- `show additions` displays all additional declarations generated during a proof.
- `rollback` reverses the effect of the last list of tactics applied.
- `reduce term T` evaluates a term `T` w.r.t. the curent module.
- `search path from S to T` searches for a rewrite path from a source term `S` to a target term `T` w.r.t. the current module.
- `qed` ends the current proof and returns to the system level.

## Tactics

CITP supports the following tactics:
- `ind(V)` for structural induction on the variable `V`.
- `red` or `reduce` for discharging the goals by applying the equations in the current specification.
- `split` for transforming a goal with multiple conclusions into several goals with a single conclusion.
- `simp` for simplyfiny the goals.
- `push(N)` or `push(ID)` for introducing premises into the current specification, where `N` stands for the index of the premise and `ID` for its identifier (given by metadata). Alternatively, it is possible to use `push-all` to introduce all premises.
- `pull(ID)` for transforming a sentence in the specification into a premise.
- `imp` for the implication tactic.
- `conj` for the conjunction tactic.
- `disj(N)` or `disj(ID)` for the disjunction tactic, where `N` stands for the index of the premise and `ID` for its identifier (given by metadata).
- `tc` for the theorem of constants.
- `sk` for Skolemization.
- `ca` for case analysis.
- `ca-rev` for case analysis reversing the order of the terms.
- `cs`  for case analysis for sequences.
- `init(ID, SB)` or `init(N, SB)`, where `SB` stands for a substitution, `N` for the index of the premise, and `ID` for its identifier (given by metadata). When the substitution can be inferred from the context the `init(ID)` tactic can be used for a particular identifier and `init-all` for all premises.
- `subst(SB)` for applying the substitution `SB` in existential quantifications.
- `trans` for transitivity.
- `@crt(T)` is used for appyling the tactic `T` only to the current goal.
- `select(N)`, with `N` the index of a goal, for selection the `N`th goal.

## License

The CITP source code is licensed under the [GNU General Public License v2.0 or later](https://www.gnu.org/licenses/old-licenses/lgpl-2.0.html).
