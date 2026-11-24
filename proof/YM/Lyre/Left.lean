import YM.QCD.Tide.Patron
import YM.Massive.RG.History
/-! # Exact bilateral adjoint, including the parity signs.
    Use transferred/nurtured *both* oriented products, not just with the
    unmarked densities. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter QCD.Lat QCD MeasureTheory Lattice Wilson QCD.Grass
open Push.GridApprox Tide Transfer
open RG Kit Kites NormedSpace
open scoped Topology ComplexOrder Matrix.Norms.L2Operator Classical
variable {A B C:Type*}[Fintype A][Fintype B][Fintype C]
-- Keep arbitrary orientations (linear) here. Rotation sign happens twice.
lemma left_side (z:Dirac (A⊕B)) (y:Dirac B):
    ber B (y*marginal A B z)=ber _ (far A B y*z):=by
   have hu(x:Dirac B)(hp:Plus x):ber B (x*marginal A B z)=ber _ (far A B x*z):=by
       have ht:Plus (far A B x):=(pass_grade ..).trans (congr_arg _ hp)
       rw [(hp.central _).symm.eq,(ht.central _).symm.eq,marginal_test] -- check direction
   have hv(x:Dirac B)(hp:Minus x):ber B (x*marginal A B z)=ber _ (far A B x*z):=by
       have ht: Minus (far A B x):=(pass_grade ..).trans ((congr_arg _ hp).trans (map_neg ..))
       have hx:x*marginal A B z=marginal A B (grade z)*x:=by rw [marginal_grade,hp.slides,grade_twice]
       have h:far A B x*z=grade z*far A B x:=by rw [ht.slides,grade_twice]
       rw [hx,marginal_test,h]
   rw [← both y, add_mul,map_add,map_add,add_mul,map_add,hu (plus y) (plus_grade y),hv (minus y) (minus_grade y)]
variable [DecidableEq A][DecidableEq B]
lemma left_shore (Q:Matrix A B ℂ)(x:Dirac B)(y:Dirac A): ber A (y*sheath 1 Q x)= ber B (furnace Q y*x):=by
   let E:=Equiv.sumComm B A
   unfold sheath; simp only [Complex.ofReal_one,inv_one, one_pow,one_smul]
   rw [left_side, ← passed E,map_mul (pass E),map_mul (pass E),show pass E (gauss (joinD 1 Q 0))=_ from swapsS Q,show pass (⇑E) (near B A x)=far A B x from AlgHom.congr_fun (pass_comp Sum.inl (⇑E)) x,show pass (⇑E) (far B A y)=near A B y from AlgHom.congr_fun (pass_comp Sum.inr (⇑E)) y,←mingler,marginal_test];
   rw [←mul_assoc ((near A B) y), ((gauss_plus _).central _).eq,mul_assoc]
lemma right_shore (Q:Matrix A B ℂ)(x:Dirac B)(y:Dirac A): ber A (sheath 1 Q x*y)= ber B (x*furnace Q y):=by
    let E:=Equiv.sumComm B A
    unfold sheath; simp only [Complex.ofReal_one,inv_one, one_pow,one_smul]
    rw [marginal_test, ← passed E,map_mul (pass E),map_mul (pass E),show pass (⇑E) (near B A x)=far A B x from AlgHom.congr_fun (pass_comp Sum.inl (⇑E)) x,show pass (⇑E) (far B A y)=near A B y from AlgHom.congr_fun (pass_comp Sum.inr (⇑E)) y,show pass E (gauss (joinD 1 Q 0))=_ from swapsS Q,←mingler,left_side,mul_assoc]
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.left_shore
#print axioms YM.Massive.Lyre.right_shore
