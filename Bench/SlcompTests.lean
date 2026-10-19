import Bench.Slcomp
open HProp Notation

-- batch run, thin wrapper for runProblem

-- set_option trace.xsimpl true in
#slcomp_run "sl-comp-bench/qf_shls_entl/bolognesa-10-e01.tptp.smt2" (timeout := 5000)
#slcomp_run "sl-comp-bench/qf_shls_entl/smallfoot-vc01.tptp.smt2" (timeout := 5000)
#slcomp_run "sl-comp-bench/qf_shls_entl/smallfoot-vc03.tptp.smt2" (timeout := 5000)
#slcomp_run "sl-comp-bench/qf_shls_entl/clones-01-e01.tptp.smt2" (timeout := 5000)
#slcomp_run "sl-comp-bench/qf_shls_entl/bolognesa-13-e10.tptp.smt2" (timeout := 5000)
#slcomp_run "sl-comp-bench/qf_shid_entl/01.tst.smt2" (timeout := 5000)
#slcomp_run "sl-comp-bench/qf_shid_entl/02.tst.smt2" (timeout := 5000)
#slcomp_run "sl-comp-bench/qf_shid_entl/ls_even_entails_ls.sb.smt2" (timeout := 5000)
#slcomp_run "sl-comp-bench/does-not-exist.smt2" (timeout := 5000)

-- this prints the names of the generated definitions
#slcomp_show "sl-comp-bench/qf_shls_entl/ls-vc05.smt2"

open Bench.Slcomp.Gen.ls_vc05_smt2

#print p_ls -- actual predicate

#print f_ls -- the functional
#print m_ls -- its monotonicity proof
#print e_ls -- unfold equation

-- inspect the generated goal interactively
#slcomp_try "sl-comp-bench/qf_shls_entl/ls-vc05.smt2" by
  intro y w
  xsearch

#check goal
