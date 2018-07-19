# CITP (The Constructor-based Inductive Theorem Prover)

The Constructor-based Theorem Prover (CITP) is a tool for proving inductive
properties of software systems specified with constructor-based logics. The
present document describes the main commands supported by CITP.

## Installing the CITP

The CITP uses [Maude](http://maude.cs.illinois.edu/w/index.php?title=The_Maude_System)
as rewriting engine. Hence, the first step is to download and install the Maude
system following the instructions [here](http://maude.cs.illinois.edu/w/index.php?title=Maude_download_and_installation).
We present a basic introduction to Maude [here](Maude)

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

| Tactic                 |     Command       |
|------------------------|-------------------|
| Simultaneous induction | **ind on V:Sort** |
| Case analysis          | **ca**            |
| Theorem of constants   | **tc**            |

## Running example

### Maude