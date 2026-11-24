import YM.Lapin.Olen
/-! Z zero-total companion. onsite symmetric difference. Normalization chosen to have base row. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.PCAC.Oren
open Function Filter MeasureTheory Set QCD QCD.Lat QCD.Grass Lattice Wilson UV RG QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator Classical TensorProduct Kronecker
open Poised Poised.Beacon Poised.Plans Finset Module Poised.Stative Massive.Patria Patria.Exposure Depth Intag
open Entr Entr.Meridian Stew Cylinder
open QCD.Tide Revolve Onsite Tawny Tawny.Cast TorusPCAC.Geometry TorusPCAC.Ward Oriole
variable {S:Scheme}{R c:Side}{d n i l j:ℕ}(A:Run S n R 6)(hA:A.Actual)
variable (a b:Flavor 6)(j:Axis)(o:Site c)
local notation "M"=> S.side R i
local notation "φ"=> A.density i
local notation "Ξ"=> actor A i
local notation "N"=> c
open QCD.Cove QCD.Creek
noncomputable def mote (V:Grid c) : EvenA c 6:= - cream (localF o 1 a a)
noncomputable def sprig (V:Grid c) : EvenA c 6:= (2:ℂ)⁻¹ • (mote a (o+step j) V-mote a (o-step j) V)
noncomputable def sprigs (j:Axis)(u:Cover) : Insertion (S.side R i) 6:=⟨fun V=> (Ξ V)*(sprig a j (wrap _ u) V).val,(Ξ).continuous.mul (by unfold sprig mote; exact continuous_const)⟩
variable (U:Grid c)
local notation "D"=> localF o 1 a a
open TorusPCAC.Jet TorusPCAC.Spin TorusPCAC.Jet.Selector
lemma κmolt(k:Frame c): slots 6 k (mote a o U).val=(mote a o U).val:=by
      let g:= Lat.rotates 6 k; have ht: Commute g D:= (commute_zone o _).symm.mul_right (commuteSpin a a 1 k); change slots 6 k (-(form D))=_; rw[map_neg]; unfold Lat.slots; rw[form_map,Matrix.transpose_transpose,ht.eq.symm,← Matrix.mul_assoc,(Lat.rotates_law ..).1,one_mul]; rfl -- order
local notation "Rho" p:arg=> TorusPCAC.Ward.acts (proclaim p) c
lemma rhyme (z:FlavorTorus) : (Rho z) (mote a o U).val=(mote a o U).val:=by
     let v:= TorusPCAC.Ward.tag c (proclaim z); have hu(i j:Modes c 6)(h:i.2≠j.2): D i j=0:=by
          have hh: ¬(i.2=a∧j.2=a):=fun h0=> h (h0.1.trans h0.2.symm); unfold localF; rw [zleft]; simp [spot,flavorW,hh]

     have ht:Commute v D:=by
           unfold Commute SemiconjBy; ext i j; unfold v TorusPCAC.Ward.tag; rw [Matrix.diagonal_mul, Matrix.mul_diagonal]; by_cases h:i.2=j.2; · rw [h,mul_comm]
           rw [hu _ _ h,mul_zero,zero_mul]
     change Kit.disguise v (-(form D))=_; rw [map_neg]; unfold Kit.disguise; rw [form_map,Matrix.transpose_transpose, ht.eq.symm, ←mul_assoc,(TorusPCAC.Ward.tag_unit ..).1,one_mul]; rfl
open TorusPCAC.Geometry.Switch TorusPCAC.Geometry.AxisB
lemma epoch_z : TorusPCAC.Stencil.charge c (mote a o U).val=(mote a o U).val:=by change TorusPCAC.Stencil.charge c (-(form D))=_; rw[map_neg]; unfold TorusPCAC.Stencil.charge; rw [shifted, Switch.tune,b_zone a o 1 (by rw[mul_one,pays_C,Matrix.transpose_one])]; rfl
-- moving the center with exact seam. rank equivariant
variable (w:Grid c)(p:Site c) (s: Signed)(l:Site c→ℂ)(T:Spike)(hL:Glare s (0:Site c) 0 p l)(hP:Swing s T)
local notation "K"=> Kit.disguise (copies 6 (hues p s l T))
local notation "X"=> shiftE s p
include hL hP
lemma fond : K (mote a o U).val=(mote a (shiftE s p o) w).val:=by
     let F:= copies 6 (hues p s l T); let V:= localF (X o) 1 a a; have ht: D*F=F*V:= w_herd _ _ _ _ _ _ _ _ _ (by simp) -- check
     change K (-(form D))= - form _; rw[map_neg]; change -(adapter F ((star F).transpose) _)=_; rw[form_map,Matrix.transpose_transpose, ht, ← mul_assoc, (Lat.copies_unitary _ _ (colour_wheel hL hP)).1,one_mul]
lemma shineJ : K (sprig a j o U).val=(↑(signT s j):ℂ) • (sprig a (s.perm j) (shiftE s p o) w).val:=by
       change K ((2:ℂ)⁻¹ • ((mote a _ _).val-(mote a _ _).val))=_; rw [map_smul,map_sub, fond a (o+step j) U w p s l T hL hP, fond a (o-step j) U w p s l T hL hP]; have ht: X (o+step j)= X o+s.act (step j):=by change affine s p _= affine s p o + _; unfold affine; rw [s.act_add]; abel -- add_comm edit
       have he:X (o-step j)= X o-s.act (step j):=by change affine s p _= affine s p o- _; unfold affine; rw[Signed.act_sub]; abel
       rw [ht,he]; by_cases hp:s.flip j=true
       · rw [show s.act (step j:Site c)=-step (s.perm j) from ?_,signT,if_pos hp]; push_cast; rw[sub_neg_eq_add,←sub_eq_add_neg,neg_one_smul]; change (2:ℂ)⁻¹ • (_-_)= - ((2:ℂ)⁻¹ • (_-_)); rw[←smul_neg,neg_sub]
         change s.act _=_; ext i; obtain ⟨k,rfl⟩:=s.perm.surjective i; rw [Signed.act_at]; by_cases h:j=k; · subst k; simp [*,step_apply]
         simp [*,step_apply,Ne.symm h]
       rw[show s.act (step j:Site c)=step (s.perm j) from ?_,signT,if_neg hp]; simp; rfl
       ext i; obtain ⟨k,rfl⟩:=s.perm.surjective i; rw [Signed.act_at]; by_cases h:j=k; · subst k; simp [*,step_apply]
       simp [*, step_apply,Ne.symm h]
end YM.Massive.PCAC.Oren
#print axioms YM.Massive.PCAC.Oren.shineJ
#print axioms YM.Massive.PCAC.Oren.κmolt
#print axioms YM.Massive.PCAC.Oren.epoch_z
#print axioms YM.Massive.PCAC.Oren.rhyme
