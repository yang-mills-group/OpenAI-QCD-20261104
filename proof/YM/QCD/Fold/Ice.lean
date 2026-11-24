import YM.QCD.Fold.Tall
/-! # Descended Grass sale. Only exact on cylindrical clusters. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Folding
open Function Lattice Wilson Lat Flume Orbit Run Fork Kit Cost Finset Relation
open PhysicalNext.Repeat.Deck Push.Local Further.PhysicalPeriodLimitF933 Macrame Shingle
open Bay Strut Sway Revolve Quarry Port RG Leaf Tee LeafM Rudder Eyrie Sparks Garden YM.Next.Free Loom
open Cove Grass
open scoped Classical Matrix Matrix.Norms.L2Operator BigOperators
variable {c C f F:Side}{D b B j k x χ N:ℕ}(X: Flight j k){e : f.val=c.val*X.L.val}{E:F.val=C.val*X.L.val}(h:C.val=c.val*D)(hl:2≤c.val)
variable (L:Window c C D)(g:Site C→ℂ)(N:ℕ)
def axes : EvenA C N →ₐ[ℝ] EvenA c N:= let Γ:= choir N (stream L g); AlgHom.restrictScalars ℝ (car (adapter Γ Γᴴᵀ) (fun x h=>(exterior_parity _ x).trans (congr_arg _ h)))
lemma carry_const (s:ℂ): axes L g N (sparkF C N s)=sparkF c N s:=by
   let B:= choir N (stream L g)
   exact map_smul (car (adapter B Bᴴᵀ) (show ∀ x,Plus x→ Plus _ from (fun x h=> (exterior_parity _ x).trans (congr_arg _ h)))) s 1 |>.trans (by rw [map_one]; rfl)
lemma choirG (x:Rail c C) (y:Sheet C)(z:Rail C c): copies N (x*y*z)=choir N x*copies N y*choir N z:=by
   unfold copies choir; rw [← Matrix.blockDiagonal_mul (M:=fun _=>x), ← Matrix.blockDiagonal_mul]
lemma carry_ψ (Y:Sheet C): axes L g N (paleF N Y)= paleF N ((stream L g)ᴴ*Y*stream L g):=by
   let A:= stream L g; let B:=choir N A; apply lit_eqn; change adapter B Bᴴᵀ (Grass.form (copies N Y))=Grass.form _; rw [form_map,Matrix.transpose_transpose, ← Matrix.mul_assoc, choirG]; congr 2; 
   ext; simp [B,A,Matrix.blockDiagonal_apply,choir, Matrix.conjTranspose_apply]
variable (d:Site F→ℂ)(hd:Quaint (Lace.project (P:=X.patch) (h:=e) (H:=E) h hl).high d)
local notation "V"=> Lace.project (P:=X.patch) (h:=e) (H:=E) h hl
local notation "r"=>sliceL X e
local notation "R"=>sliceL X E
variable {Q:Plan j}{P:Plan k}{t z a p A m q w u η p' z' A' Ω Ω' ℓ:ℝ}{Z : Offer 1 t p}{U':Offer 2 a A}{J:ℕ→Atom su 2}
variable (Y: Swathe X E (park X E Q Z U' z m) J P w z' η Ω Ω' b)
variable (S: Swathe X e (park X e Q Z U' z m) J P w z' η Ω Ω' b)
local notation "Q'"=> pressL (X:=X.patch) (E:=E) (e:=e) h hl d
local notation "A₀"=> anchL (X:=X.patch) (E:=E) (e:=e) h hl d
variable (hv:Species X E w p' z' η ℓ x (park X E Q Z U' z m))(hp:Species X e w p' z' η ℓ x (park X e Q Z U' z m))(hT:0<t)(hA:0<a)(hz:0<z)(hq:z≤1)(hB:4*B+3<f.val)(hs:0<z')
variable (he:S.walk=(anchL (X:=X.patch) (E:=E) (e:=e) h hl d).cloud Y.walk b B)(hX:S.bath=(pressL (X:=X.patch) (E:=E) (e:=e) h hl d).cloud Y.bath b B)
include he hd hv hp hT hA hz hq hB hs
lemma tableZ (p: Site F)(J':Grid f): spoon S.walk ((V).high.cut p) B ((V).high.cut p) ((V).high.cut p) (settled J')=spoon Y.walk p B p p (settled ((V).high.links J')):=by
   rw [he]; have hm:= (A₀).forks p ((A₀).pi p) J' (A:=sun r) (fun i j he=>peaksL h hl d hd i j he) (line_support (X:=X.patch) h hl d hd (fun i=> probed X h hl d hd hv hp hT hA hz hq i J)) Y.puff Y.att hB hs
   have ht:= hm.1; refine ht.trans ?_; rw [sum_eq_single p]; rotate_left
   · intro i hi hv'; suffices hh : spoon Y.walk p B p i (settled ((V).high.links J'))=0 by exact (congr_arg ((A₀).rim p i • ·) hh).trans (smul_zero _)
     have h := (trimming Y.att p B p i); by_contra H; have hm := (lt_of_lt_of_le (norm_pos_iff.mpr H) (h.2.2.2.1 _ (citizenship _ hs _))).ne'; have hz : separation p i ≤ B:=(tendle ..).1 (h.2.1 hm).2; exact hv' (tiniest (A₀).d ((posted ..).1 hi) (separation_comm p i ▸ (by omega)))
   · simp
   have he:(A₀).rim p p=1:=by change star (d p)*d p=_; rcases hd.sign p with h|h<;>rw[h]<;>simp
   rw [he,one_smul]; rfl
set_option quotPrecheck false
local notation "Θ"=> axes (V).low (d ∘ (R).embed) N
lemma walks_ψ (o:Site F) (U:Grid f): Θ (broke Y N B (.inl (o,none)) ((V).high.links U))=broke S N B (.inl ((V).high.cut o,none)) U:=by
   unfold broke; rw [map_sub,map_one,NormedSpace.map_exp Θ ((Θ).toLinearMap.continuous_of_finiteDimensional)]; simp only [sliceF,Sum.elim_inl,carry_const,chalkF,chipK]; rw [tableZ X h hl d hd Y S hv hp hT hA hz hq hB hs he o U, tableZ X h hl d hd Y S hv hp hT hA hz hq hB hs he o 1]; rfl -- arg order N check
include hX
omit he
lemma bath_ψ (o:Site C)(U:Grid f): Θ (broke Y N B (.inr (o,none)) ((V).high.links U))=broke S N B (.inr ((V).low.cut o,none)) U:=by
   have hh := forge (Q') (V).low (consumes (P:=P) X h hl d hd hv hp hT hA hz hq) Y.arcP Y.glow (A:=dot r) (fun i j he=>dunes h hl d hd i j he) hB R r rfl (fun i=>rfl) (fun i=>rfl) U o hs
   unfold broke; rw [map_sub,map_one, NormedSpace.map_exp Θ ((Θ).toLinearMap.continuous_of_finiteDimensional)]; simp only [sliceF,Sum.elim_inr,hX]; rw [carry_ψ,Matrix.mul_neg,Matrix.neg_mul]; rw [show batch r ((Q').cloud _ _ _) ((V).low.cut o) none B (settled U)= _ from hh]; rfl
end YM.QCD.Folding
