Prerequisites
-------------

In addition to the [Coq proof assistant](https://coq.inria.fr/) (>= 8.8),
you need the following libraries:

- [Mathematical Components](http://math-comp.github.io/math-comp/) (>= 1.6),
- [Flocq](http://flocq.gforge.inria.fr/) (>= 3.1),
- [Coquelicot](http://coquelicot.saclay.inria.fr/) (>= 3.0)
- [BigNums](https://github.com/coq/bignums/)

The `.tar.gz` file is distributed with a working set of configure files. They
are not in the git repository though. Consequently, if you are building from
git, you will need `autoconf` (>= 2.59).


Configuring, compiling and installing
-------------------------------------

Ideally, you should just have to type:

    ./configure && ./remake --jobs=2 && ./remake install

The environment variable `COQC` can be passed to the configure script in order
to set the Coq compiler command. The configure script defaults to `coqc`.
Similarly, `COQDEP` can be used to specify the location of `coqdep`. The
`COQBIN` environment variable can be used to set both variables at once.

The library files are compiled at the logical location `Interval`. The
`COQUSERCONTRIB` environment variable can be used to override the
physical location where the `Interval` directory containing these files
will be installed by `./remake install`. By default, the target directory
is `` `$COQC -where`/user-contrib ``.
