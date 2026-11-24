import YM.Clink.Rune
/-! Actual tilde.Family. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.PCAC.Oren
open Function Filter MeasureTheory Set QCD QCD.Lat QCD.Grass Lattice Wilson UV RG QCD.Grass.Ward
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator Classical TensorProduct Kronecker
open Poised Poised.Beacon Poised.Plans Finset Module Poised.Stative Massive.Patria Patria.Exposure Depth Intag
open Entr Entr.Meridian Stew Cylinder
open QCD.Tide Revolve Onsite Tawny Tawny.Cast TorusPCAC.Geometry TorusPCAC.Ward Oriole
open Next.Free QCD.Flume TorusPCAC.Jet TorusPCAC.Spin TorusPCAC.Jet.Selector Switch AxisB
variable {c:Side}(d:ℕ)(P:Plan d)(H:Train d)(m:ℝ)(o:Site c)(a:Flavor 6)(x:Axis)(V:Grid c)
local notation "S"=> cedar d P H m c
local notation "R"=> forkT
local notation "F"=> forkT a o x (cedar d P H m c)
lemma fogue : Continuous (R a o x (cedar d P H m c)):=by
       rw [show R a o x S=fun V=> bouquet a (scans o x S V) from funext fun V=> yields o a x V S]; apply Continuous.comp (bouquet a).continuous; unfold scans peakZ Stew.delta; have hp:= cedarC (c:=c) d P H m; fun_prop -- priest
local notation "Rho" z:arg=> TorusPCAC.Ward.acts (proclaim z) c
lemma σeve (z:FlavorTorus) : (Rho z) (F V).val=(F V).val:=by
       rw [yields]; let X:= scans o x S V; let M:= capsΛ a X; let T:= TorusPCAC.Ward.tag c (proclaim z); have hu(i j:Modes c 6)(h:i.2≠ j.2): M i j=0:=by
            have he: ¬(i.2=a ∧ j.2=a):=fun h₁=>h (h₁.1.trans h₁.2.symm); change (X ⊗ₖ spot a a) i j=0; simp [spot,he]
       have hp:T*M=M*T:=by
            ext i j; unfold T TorusPCAC.Ward.tag; rw [Matrix.diagonal_mul, Matrix.mul_diagonal]; by_cases h:i.2=j.2; rw [h,mul_comm]; rw[hu _ _ h,mul_zero,zero_mul]
       change Kit.disguise T (QCD.Grass.form M)= QCD.Grass.form M; unfold Kit.disguise; rw[form_map,Matrix.transpose_transpose,← hp, ← Matrix.mul_assoc,(TorusPCAC.Ward.tag_unit ..).1,one_mul]
local notation "U" g:arg=> Lattice.gauge g V
lemma anthem(g:Frame c): slots 6 g (F (U g)).val=(F V).val:=by
       let G:= siteRot g; rw [yields,yields]; change Kit.disguise (copies 6 G) _= _; let X:= S (U g); have hv:X*G=G*S V:=by unfold X; rw[ash]; rw[mul_assoc,(siteRot_u ..).1,mul_one]
       have ht:punct o*G=G*punct o:=by unfold punct G siteRot; rw [ride_mul,ride_mul]; congr 1; funext j; split_ifs<;> try simp_all -- expensive
       have hx: delta (U g) x *G=G*((1:ℂ) • delta V x):=by rw[one_smul]; exact gate_delta .. -- arg n wrong
       rw [auraB _ _ _ (siteRot_u ..), scans,κfactor _ _ _ _ _ _ _ _ G hx hv ht (siteRot_u ..),one_smul]; rfl
variable (p:Site c) (w:Signed) (l:Site c→ℂ)(T:Spike)(hL: Glare w (0:Site c) 0 p l)(hT:Swing w T)
local notation "M"=> Kit.disguise (copies 6 (hues p w l T))
local notation "t"=> shiftE w p
local notation "Z"=> pull w p V
local notation "v"=> ((signT w x:ℝ):ℂ)
include hT hL
lemma favors : M (F Z).val= v • (R a (t o) (w.perm x) S V).val:=by
        let A:= hues p w l T; let D:= punct o; have ht: D*A=A*punct (t o):=by
             unfold D punct A hues; rw [ride_mul,ride_mul, Equiv.refl_trans,Equiv.trans_refl]; apply congr_arg; funext i; simp only[Equiv.refl_apply, Equiv.apply_eq_iff_eq, Equiv.eq_symm_apply]; by_cases h:i=o <;> simp [*, (shiftE w p).injective.eq_iff,Ne.symm] -- simp
        have hu: S Z*A=A*S V:=by rw [elm d P H m V w p l T hL hT,mul_assoc,(colour_wheel hL hT).1,mul_one]
        have hp: Stew.delta Z x*A=A*(v • delta V (w.perm x)):= (swivel p w l x T hL V).trans (Matrix.mul_smul ..|>.symm)
        rw [yields,yields,auraB _ _ _ (colour_wheel hL hT),scans,κfactor _ _ _ _ _ _ _ _ _ hp hu ht (colour_wheel hL hT),map_smul]; rfl
end YM.Massive.PCAC.Oren
#print axioms YM.Massive.PCAC.Oren.favors
#print axioms YM.Massive.PCAC.Oren.σeve
#print axioms YM.Massive.PCAC.Oren.anthem
