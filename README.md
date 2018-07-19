# CITP (The Constructor-based Inductive Theorem Prover)

The Constructor-based Theorem Prover (CITP) is a tool for proving inductive
properties of software systems specified with constructor-based logics. The
present document describes the main commands supported by CITP.

## Installing the CITP

The CITP uses [Maude](http://maude.cs.illinois.edu/w/index.php?title=The_Maude_System)
as rewriting engine. Hence, the first step is to download and install the Maude
system following the instructions [here](http://maude.cs.illinois.edu/w/index.php?title=Maude_download_and_installation).
We present a basic introduction to Maude [here](#maude).

Once Maude has been installed (we assume a **maude** command for executing it),
we can download the CITP repository by using

```
git clone https://github.com/ittutu/CITP
```

This command creates a folder **CITP** in our computer. Among others, it contains
the subfolder **Tool**, which contains the source code of the tool in the
**citp.maude** file, and the subfolder **Examples**, with several examples that can
be executed by users to test the tool. For example, to run the **TAS** example we
should do as follows:

```
maude Tool/citp.maude

cd CITP/Examples/tas_exercise
load tas.maude

select #CITP# .
loop init .
```

The first command starts Maude and loads the CITP. The second command sets the current
folder as the one containing the tas example, while the third one loads the module into
Maude. This module contains the simple mutual exclusion protocol *test&set*, which we
will explain in detail later.
Finally, the last two commands select the tool and initiate it, so we can start
introducing commands.

## Using the CITP

In the following we present how to introduce and prove goals in CITP.
It is important to note that all the commands presented here must be introduced in
the tool enclosed in parentheses, so they can be parsed by the CITP.

### Goals

All proofs start by introducing a goal. In CITP, goals are sets of sentences related
to a given module. The syntax for introducing goals is

```
goal MOD-NAME |-
SENT1 ;
...
SENTn ;
```

where `MOD-NAME` is the name of the module where the proof takes place and
`SENT1` ... `SENTn` are the sentences the goal is composed of. These sentences
can be either equations, membership axioms, and rewrite rules.

### Proof tactics

We present next the tactics available in CITP. In general, we will not apply
single tactics but tactic lists of the form **(tc1 ... tcn)**, where each **tci**
is a single tactic.

Note that CITP handles
a set of goals of the form **(goal M |- SS)**, with **M** a module and **SS** a
set of sentences. In contrast to other provers, CITP does not keep a tree structure
and list of tactics will be applied to all goals.

If the user wants to apply the tactic list only to the current goal then the
command **(. tc1 ... tcn)** can be used. Moreover, we can change the current goal
with **(select N)**, which selects the **N**th goal as current one.

#### General proof tactics

The general proof tactics, described in the table below, are sound for all
specifications. It is important to note that

Some details about these commands are:

* *Simultaneous induction* has syntax `ind on V:Sort`, for `V:Sort` a variable
appearing in the goal. The cases are generated by using the operators marked with
the **ctor** atribute in the specification.
* The *theorem of constants* replaces all variables by fresh constants and
splits the sentences in the same goal in several goals.
* *Case analysis* splits the goals by using the conditions of conditional
sentences. It assumes the conditions are disjointly true and the left-hand
side of the sentences is equal.
* *Implication* adds the conditions in the sentences of the goal to the module.
* *Reduction* reduces by rewriting both sides of the current goal.
* *Initialization* has syntax `init sen by sub`, for a sentence `sen` and a
substitution `sub`, gives concrete values to the variables in the sentence.
* *Critical pairs left* has syntax **(cp-l sentence1 >< sentence2)** tries to unify
a subterm of **sentence1** with the left-hand side of **sentence2**.
**cp-r** works analogously for the right-hand side.

| Tactic                 |     Command       |
|------------------------|-------------------|
| Simultaneous induction | **ind on**        |
| Theorem of constants   | **tc**            |
| Case analysis          | **ca**            |
| Implication            | **imp**           |
| Reduction              | **red**           |
| Initialisation         | **init**          |
| Critical pairs left    | **cp-l**          |
| Critical pairs right   | **cp-r**          |

#### Specific proof tactics

The specific proof tactics, listed in the table below, are sound for initial data
types that are often used in applications such as sequences/lists, sets and pairs
as long as they are protected.

It is important to note that these tactics are designed for goals consisting of a
specification and a single formula: **ca, tc, imp, red, cs, pair**. However, if one
of these tactics is applied to a goal of the form **M |- {E1,...,En}**, the goal
is decomposed into a list of subgoals **(M |- E1), ..., (M |- En)** and then the
tactic is applied to each goal **M |- Ei*.

| Tactic                               | Command  |
|--------------------------------------|----------|
| Induction based on membership axioms | **indx** |
| Case analysis for sequences and sets | **cs**   |
| Pair                                 | **pair** |

#### Interface commands

In addition to the commands for developing the proof, CITP provides commands
for interacting with the interface, as shown by the table below.

| Command          | Description                                                                      |
|------------------|----------------------------------------------------------------------------------|
| **rollback**     | Returns the proof process to the state before applying the last list of tactics. |
| **show goals**   | Displays the goals to discharge.                                                 |
| **show proof**   | Shows the sequence of lists of tactics applied                                   |
| **redTerm t**    | Reduces the term **t** to its normal form  w.r.t. the current module.            |

