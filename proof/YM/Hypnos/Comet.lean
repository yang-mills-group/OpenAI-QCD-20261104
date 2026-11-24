import YM.Hypnos.Rot
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Leaf.Tee
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees Pressure
open Garden Spice Jets Sun LeafM
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y w p ε α β t:ℝ}{l b r:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
namespace Rot
open Eyrie Revolve Rudder Cost
-- polymer.P X.H.P.F.D. eligible high.short support
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "S"=> sliceL G h
variable {T:Grid f→Sheet f}(P: Plan j){X: Offer 1 α x}{Y:Offer 2 β y}{t₀ m:ℝ}
local notation "Q"=>pesto P G h (trunkM X Y t₀ m f)
variable (P':Sun G c f h δ v q u a l (pesto P G h (trunkM X Y t₀ m f)))
include P' in
lemma copy_n (i j:A) :
   ‖copies F ((Q 1)⁻¹) i j - spider F G h i j‖ ≤ (stamp P G.L)*|m| *a⁻¹:=by
    let T:=Q 1; let B':= father G h; let S':=stamp P G.L *|m| *a⁻¹
    have hv:T=B'+(m:ℂ) • 1:=by unfold T pesto trunkM blossomT; simp only [Pi.add_apply,Pi.smul_apply]; rw [Fork.pale (frosting X.W) (by decide),Fork.pale (frosting Y.W) (by decide),tree_zero,add_zero,zero_add]; rfl
    have hx:=P'.stable; have he:IsUnit B'.det:=by unfold B'; rw [← tree_zero P]; exact ticket_inv ..
    have hg : ‖B'⁻¹‖≤ stamp P G.L:=by unfold B'; rw [← tree_zero P]; exact ticket_B ..
    have hH : ‖T⁻¹‖≤ a⁻¹:=(hx.terrific 1).reciprocal hx.calf; have hz:=hx.sole 1
    have hy : ‖T⁻¹-B'⁻¹‖ ≤ S':=by
       rw [show T⁻¹-B'⁻¹= -(B'⁻¹*(T-B')*T⁻¹) by rw [mul_sub,sub_mul,mul_assoc B'⁻¹ T,Matrix.mul_nonsing_inv T hz,mul_one,Matrix.nonsing_inv_mul B' he,one_mul,neg_sub], show T-B'=(m:ℂ) • 1 by rw [hv]; abel,norm_neg]
       have ht:= (norm_nonneg _).trans hg
       refine (norm_mul_le ..).trans (mul_le_mul ((norm_mul_le ..).trans (mul_le_mul hg ?_ (norm_nonneg _) ht)) hH (norm_nonneg _) (by positivity))
       rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,oneNorm,mul_one]
    by_cases hp:i.2=j.2
    · have he (M:Sheet f): copies F M i j=M i.1 j.1:= if_pos hp
      rw [he,spider,he]; exact (Cost.north (T⁻¹-B'⁻¹) i.1 j.1).trans hy
    have he (M:Sheet f): copies F M i j=0:= if_neg hp; rw [he,spider, he,sub_zero,norm_zero]; exact (norm_nonneg _).trans hy

lemma spate (ht:0≤u)(U:Grid f)(i j:A)(hw:beamAt (trunkFt i.1.1 r) U 1 w)(hz:0 ≤ w)(hδ:w <δ/2):
   ‖spore P' r U i j-spider F G h i j‖ ≤ q*(w/(δ/2))+(Real.exp (-u*fossil r l)* q+(stamp P G.L)* |m| *a⁻¹):=
    (norm_sub_le_norm_sub_add_norm_sub _ (spore P' r 1 i j) _).trans (add_le_add (verandah P' ht U i j hw hz hδ) ((norm_sub_le_norm_sub_add_norm_sub _ (copies F ((Q 1)⁻¹) i j) _).trans (add_le_add (vine_cost P' r ht _ _ _) (copy_n P P' i j))))

-- direct bound inside cropped REAL. Outside replace by zero with expo for any instance. Keep both types.
lemma wreath (ht:0≤u)(U:Grid f)(i:Keys f F)(j: Keys c F) (hw:beamAt (trunkFt (locationP i) r) U 1 w)(hz:0 ≤ w)(hδ:w <δ/2):
    ‖((P'.equip F r).shortP U) i j-wheelsF F G h i j‖ ≤ stamp P G.L * |m| *a⁻¹*massL G.L+(Real.exp (-u*fossil r l)+w/(δ/2))*q:=by
    let M:= stamp P G.L * |m| *a⁻¹*massL G.L; let Aₓ:= Real.exp (-u*fossil r l)+w/(δ/2); have hA:0 ≤ Aₓ:= add_nonneg (Real.exp_pos _).le (div_nonneg hz (half_pos P'.positive).le)
    obtain ⟨h,h'⟩:= fees P'.stable
    have hk:0≤M+Aₓ*q:= add_nonneg ((norm_nonneg _).trans (h 0 0)) (mul_nonneg hA P'.stable.forest.le); change ‖short P'.Z P'.V _ _ _ _-foamB _ _ _ _‖≤_; unfold short
    rcases i with i|i <;> rcases j with j|j
    · simp only [foamI]; split
      next hp =>
        exact le_trans (Cost.north (spoon P'.Z i.1.1 _ i.1.1 j.1.1 (settled U)- cell (proton G ‹_›) i.1.1 j.1.1) i.1.2 j.1.2) ((inside_fee P'.Z0 i.1.1 _ _ P'.positive ht (Or.inl rfl) U hw hz hδ (h _ _)).trans (add_le_add_right (mul_le_mul_of_nonneg_left (packet P'.Z0 ht ..).2 hA) _))
      rw [sub_zero,norm_zero]; exact hk
    · simpa only [foamLR,sub_zero,norm_zero] using hk
    · simpa only [foamRL,sub_zero,norm_zero] using hk
    simp only [foamR]; split
    next hp =>
        refine (Cost.north (spoon P'.V i.1.1 _ j.1.1 i.1.1 (settled U) - cell (barP G _) j.1.1 i.1.1) j.1.2 i.1.2).trans ((inside_fee P'.V0 i.1.1 _ _ P'.positive ht (Or.inr rfl) U hw hz hδ (h' _ _)).trans (add_le_add_right (mul_le_mul_of_nonneg_left (packet P'.V0 ht ..).2 hA) _))
    rw [sub_zero,norm_zero]; exact hk
-- deterministic.K output cut. locationP separation.
def shear (G:Flight j k) (h:f.val=c.val*G.L.val) (F r:ℕ) : Water c f F := Matrix.of (fun i j => if (sliceL G h).embed (locationP j)∈trunkFt (locationP i) r then wheelsF F G h i j else 0)
def shore (G:Flight j k) (h:f.val=c.val*G.L.val)(F r:ℕ): Matrix (Modes f F) (Modes f F) ℂ:= Matrix.of fun i j=> if j.1.1∈ trunkFt i.1.1 r then spider F G h i j else 0
lemma spliceW (ht:0≤u)(U:Grid f)(i:Keys f F)(j:Keys c F) (hw:beamAt (trunkFt (locationP i) b) U 1 w)(hz:0 ≤ w)(hδ:w <δ/2):
    ‖((P'.equip F b).shortP U) i j - shear G h F b i j‖ ≤ stamp P G.L *|m| *a⁻¹*massL G.L +(Real.exp (-u*fossil b l)+w/(δ/2))*q :=by
    have hy:= wreath P P' ht U i j hw hz hδ
    unfold shear; rw [Matrix.of_apply]; split
    · exact hy
    next hh => rw [show (P'.equip F b).shortP U i j=0 from by_contra fun hi=> hh ((P'.equip F b).sleeps i j U hi),sub_zero,norm_zero]; exact le_trans (norm_nonneg _) hy
lemma spliceS (ht:0≤u)(U:Grid f)(i j:A)(hw:beamAt (trunkFt i.1.1 b) U 1 w)(hz:0 ≤ w)(hδ:w <δ/2):
    ‖spore P' b U i j-shore G h F b i j‖ ≤ q*(w/(δ/2))+(Real.exp (-u*fossil b l)*q+stamp P G.L * |m| *a⁻¹):=by
    have hy:= spate P P' ht U i j hw hz hδ
    unfold shore; rw [Matrix.of_apply]; split
    · exact hy
    next hh=> rw [show spore P' b U i j=0 from by_contra fun hi=> hh (spine P' _ _ _ hi),sub_zero,norm_zero]; exact le_trans (norm_nonneg _) hy
-- Row sum of FULL minus cut. with pure.Shell Species
variable (H: Sun G c f h δ v q u a l (vaultF P G h 0))
include H in
lemma fans (hZ:0≤u)(b:ℕ)(i j:A): ‖spider F G h i j-shore G h F b i j‖≤ Real.exp (-u*fossil b l)*q:=by
    have hf:=vine_cost H b hZ 1 i j
    unfold shore; rw [Matrix.of_apply]; split
    · rw [sub_self,norm_zero]; exact (norm_nonneg _).trans hf
    next hh =>
       rw [show spore H b 1 i j=0 from by_contra (fun hi=> hh (spine H _ _ _ hi)), tree_zero P,zero_sub,norm_neg] at hf; rw [sub_zero]; exact hf
lemma finance (i j:A): ‖spider F G h i j‖≤stamp P G.L :=by
    have hg:= ticket_B P G h 0 1; rw [tree_zero] at hg -- check args
    unfold spider; change ‖(if _ then _ else (0:ℂ))‖ ≤_; split; exact (Cost.north ..).trans hg
    rw [norm_zero]; exact (norm_nonneg _).trans hg
include H
lemma fungi (hZ:0≤u)(i:Keys f F): ∑ j:Keys c F, ‖wheelsF F G h i j‖ ≤ fingers F*q:=by
    let T:=vaultF P G h 0
    have hP:rightL G h T 1=proton G h:=by unfold rightL T inverser; rw [tree_zero P]; rfl
    have hP' : leftL G h T 1=barP G h:=by unfold leftL T inverser; rw [tree_zero P]; rfl
    cases i
    next i=>
       unfold wheelsF; rw [← hP,← hP']; refine (foam_at _ _ i _ (fun j=> (packet H.Z0 hZ i.1.1 j).1) q (H.Z0.spends i.1.1)).1 fun j=> ?_
       rw [← H.Z0.sells _ _ 1]; exact (norm_sum_le _ _).trans (sum_le_sum fun s _=> ((H.Z0.crop _ _ _).2.2.2.1 (settled 1) (citizenship f H.positive _)).trans (le_mul_of_one_le_left (H.Z0.crop ..).1 (market hZ l s)))
    next i=>
       unfold wheelsF; rw [← hP,← hP']; refine (foam_at _ _ i _ (fun j=> (packet H.V0 hZ j i.1.1).1) q (H.V0.dues i.1.1)).2 fun j=> ?_
       rw [← H.V0.sells _ _ 1]; exact (norm_sum_le _ _).trans (sum_le_sum fun s _=> ((H.V0.crop _ _ _).2.2.2.1 (settled 1) (citizenship f H.positive _)).trans (le_mul_of_one_le_left (H.V0.crop ..).1 (market hZ l s)))
lemma strobes (hZ:0≤u)(b:ℕ)(i:Keys f F): (∑ j:Keys c F, ‖wheelsF F G h i j-shear G h F b i j‖) ≤ fingers F*(Real.exp (-u*fossil b l)*q):=by
    let X':Water c f F := short H.Z H.V b (settled 1); have hm:∑ j:Keys c F, ‖wheelsF F G h i j-shear G h F b i j‖ ≤ ∑ j:Keys c F, ‖X' i j - wheelsF F G h i j‖:=by
       apply sum_le_sum; intro j _; unfold shear; rw [Matrix.of_apply]; split
       · rw [sub_self,norm_zero]; exact norm_nonneg _
       next hv=> rw [show X' i j=0 from by_contra (fun hi=>hv (lightS H _ _ (citizenship f H.positive _) i j hi)),sub_zero,zero_sub,norm_neg]
    let Z x j:=spoon H.Z x b x j (settled 1)-cell (proton G h) x j; let V j x:=spoon H.V x b j x (settled 1)-cell (barP G h) j x
    let E:= Real.exp (-u*fossil b l); have hx : X'-wheelsF F G h=foamB Z V:=by
       ext i j; change X' i j - wheelsF F G h i j = foamB Z V i j; rcases i with i|i <;> rcases j with j|j <;> simp only [X',short,wheelsF,foamI,foamR,foamRL,foamLR, V,Z] <;> first| exact sub_zero _ | split<;>simp
    have hv i j : cell (proton G h) i j=cell (rightL G h (vaultF P G h 0) 1) i j:=by unfold rightL inverser; rw [tree_zero]; rfl
    have hg i j : cell (barP G h) i j=cell (leftL G h (vaultF P G h 0) 1) i j:=by unfold leftL inverser; rw [tree_zero]; rfl
    apply le_trans hm; simp_rw [← Matrix.sub_apply,hx]; cases i
    next i=>
       refine (foam_at Z V i (fun j=> E*duel H.W i.1.1 j u l) (fun j=>mul_nonneg (Real.exp_pos _).le (packet H.Z0 hZ i.1.1 j).1) (E*q) ?_).1 (fun j=>?_)
       · rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (H.Z0.spends ..) (Real.exp_pos _).le
       unfold Z; rw [hv]; exact mismatch H.Z0 _ _ _ _ (Or.inl rfl) hZ H.positive _
    next i=>
       refine (foam_at Z V i (fun j=> E*duel H.B0 j i.1.1 u l) (fun j=>mul_nonneg (Real.exp_pos _).le (packet H.V0 hZ j i.1.1).1) (E*q) ?_).2 (fun j=>?_)
       · rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (H.V0.dues ..) (Real.exp_pos _).le
       unfold V; rw [hg]; exact mismatch H.V0 _ _ _ _ (Or.inr rfl) hZ H.positive _
end Rot
end YM.QCD.Leaf.Tee
#print axioms YM.QCD.Leaf.Tee.Rot.strobes
#print axioms YM.QCD.Leaf.Tee.Rot.fans
#print axioms YM.QCD.Leaf.Tee.Rot.spliceS
#print axioms YM.QCD.Leaf.Tee.Rot.spliceW
