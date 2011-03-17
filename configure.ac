AC_INIT([Interval], [0.13.0],
        [Guillaume Melquiond <guillaume.melquiond@inria.fr>],
        [interval])
AM_INIT_AUTOMAKE

m4_divert_push(99)
if test "$ac_init_help" = "long"; then
  ac_init_help=short
fi
m4_divert_pop(99)

m4_divert_push([HELP_ENABLE])
Fine tuning of the installation directory:
AS_HELP_STRING([--libdir=DIR], [library @<:@DIR=`$COQC -where`/user-contrib/Interval@:>@])
m4_divert_pop([HELP_ENABLE])

AC_ARG_VAR(COQC, [Coq compiler command [coqc]])
AC_CHECK_TOOL(COQC, coqc)

AC_ARG_VAR(COQDEP, [Coq dependency analyzer command [coqdep]])
AC_CHECK_TOOL(COQDEP, coqdep)

AC_MSG_CHECKING([for Flocq])
AS_IF(
  [ echo "Require Fcore Fcalc_digits." > conftest.v
    "$COQC" conftest.v > conftest.err ],
  [ AC_MSG_RESULT([yes]) ],
  [ AC_MSG_RESULT([no])
    AC_MSG_ERROR([ *** Unable to find the Flocq library (http://flocq.gforge.inria.fr/)])])
rm -f conftest.v conftest.vo conftest.err

if test "$libdir" = '${exec_prefix}/lib'; then
  libdir='`$(COQC) -where`/user-contrib/Interval'
fi

AC_SUBST(COQRFLAG, ['-R . Interval'])
AC_ARG_ENABLE([prefix], AS_HELP_STRING([--disable-prefix], [do not compile files into an Interval module]),
  [if test "$enable_prefix" = "no"; then COQRFLAG= ; fi], [])

AC_CONFIG_FILES([Makefile src/Makefile testsuite/Makefile])
AC_OUTPUT
