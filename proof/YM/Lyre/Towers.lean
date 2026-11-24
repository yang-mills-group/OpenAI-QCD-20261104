import YM.Lyre.Reach
import YM.QCD.Plum.Rind
/-! # multi-level bilateral maps -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lyre
open Function Filter Lattice Wilson MeasureTheory QCD QCD.Lat QCD.Tide QCD.Grass
open Transfer
open scoped Topology BigOperators Matrix.Norms.L2Operator Classical
variable {S:Scheme}{R:Side}{N F i j:ℕ}(A:Run S N R F)
local notation "f"=> S.side R
local notation "P" k=> S.step k
-- finer circumference
noncomputable def retract (i:ℕ)(x: Stud (f i) F):Stud (f (i+1)) F := Tide.offer (P i) S.choices (S.sides_next R i) (A.β (i+1)) (stampC x (A.w i)⁻¹)
lemma retractS (x: Stud (f i) F)(h:Stays x): Stays (retract A i x):= offers _ _ (S.admissible i) _ (paysA x h)
lemma retractF (X:Set (Site (f i)))(Y:Set (Site (f (i+1)))) (x: Stud (f i) F) (h:Plum.Fence X x)(hp:∀ z∈ X, Push.GridApprox.window ((QCD.Flume.sliceL (P i) (S.sides_next R i)).embed z) (Tide.fuel (P i).patch)⊆ Y) : Plum.Fence Y (retract A i x) := ⟨retractS _ x h.hp, offerL _ _ (S.admissible i) (stampC x _) (paysA _ h.hp) X Y (stageS X x h.he) hp, rolly _ _ (S.admissible i) _ (paysA _ h.hp) (stageN _ h.hz)⟩
lemma retract_one : retract A i 1=1 :=by
   have hx : stampC (1:Stud (f i) F) (A.w i)⁻¹=1 := funext fun v=> map_one (patternC _ _ _)
   unfold retract offer; rw [hx]; funext U; let Z:= (P i).visit S.choices (S.sides_next R i); let β:= A.β (i+1)
   rw [show brook Z β (1:Stud (f i) F) U=1 from ?_]; unfold furnace; change QCD.Grass.adapter _ _ (winter _ (1:Lat.Fields _ _))=_; rw [show winter (Modes (f i) F) (1:Lat.Fields _ _)=1 from cheers _,map_one]; rfl
   unfold brook; simp only [Pi.one_apply,integral_smul_const,(Z.isKernel (S.admissible _) _).total,one_smul]
lemma retreats (x:Stud (f i) F)(y)(hx:Stays x)(hy:Stays y): retract A i (x+y)=retract A i x+retract A i y:=by
    let t:= (A.w i)⁻¹; have hv: stampC (x+y) t=stampC x t+ stampC y t:= funext fun i=>map_add (patternC _ _ _) _ _; unfold retract offer; rw [show stampC (x+y) _=_ from hv]; funext U; let Z:= (P i).visit S.choices (S.sides_next R i)
    unfold brook; simp only [Pi.add_apply,smul_add]; rw [integral_add (deltaPay (S:=Z) (S.admissible _) (stampC x _) (paysA _ hx) U) (deltaPay (S:=Z) (S.admissible _) (stampC y _) (paysA _ hy) U),map_add]
lemma retreat (x:Stud (f i) F)(t:ℂ): retract A i (t • x) = t • retract A i x:=by
    unfold retract offer brook; rw [show stampC (t • x) _= t • stampC x (A.w i)⁻¹ from funext fun v=> map_smul (patternC _ _ (A.w i)⁻¹) t (x v)]; funext U; dsimp only [Pi.smul_apply]; simp_rw [smul_comm _ t, integral_smul,map_smul]
lemma wrought (p:Bool)(x:Stud (f i) F)(h:∀ U,Grass.Hom p (x U))(hp:Stays x): ∀ V,Grass.Hom p (retract A i x V):=by
    intro V
    let X:=stampC x (A.w i)⁻¹; let g(c:Side):=grade (A:=Pairs (Modes c F))
    let L(c:Side):Lat.Fields c F→L[ℝ] Lat.Fields c F:= ((g c).toLinearMap.toContinuousLinearMap).restrictScalars ℝ
    let p':ℂ:=if p then -1 else 1
    have hx(U):L (f i) (X U)=p' • X U:=by
        change grade (changeVars _ (x U))=_; rw [changeVars,exterior_parity,(hom_iff _ _).mp (h U),map_smul]; rfl
    let T:=(P i).visit S.choices (S.sides_next R i); let Y:=brook T (A.β (i+1)) X V; have hY : grade Y=p' • Y:=by
        change L _ (∫ U, _ ∂prior su _)=p' • ∫ U, _ ∂prior su _; rw [← (L (f i)).integral_comp_comm (deltaPay (S:=T) (S.admissible i) X (paysA _ hp) V), ← integral_smul]; simp_rw [map_smul,hx,smul_comm _ p']
    rw [hom_iff]; let q:= QCD.Jets.ater (P i) (F:=F) (S.sides_next R i) V -- check namespace
    change Grass.grade (Tide.furnace _ Y)=p' • Tide.furnace _ Y; rw [← mingler,← marginal_grade,map_mul,(show Grass.grade (gauss _)=_ from gauss_plus _),near, pass_grade,hY,map_smul,mul_smul_comm,map_smul] -- likely `near`
lemma retract_mult (X Y:Set (Site (f i))) (x y:Stud (f i) F)(hx:Plum.Fence X x)(hy:Plum.Fence Y y)(h:Disjoint X Y): retract A i (x*y)=retract A i x* retract A i y:=by
    unfold retract; rw [show stampC (x*y) _= stampC x (A.w i)⁻¹ * stampC y (A.w i)⁻¹ from funext fun i=>map_mul _ _ _]; exact acrossH _ _ (S.admissible _) X Y _ _ (paysA _ hx.hp) (paysA _ hy.hp) (stageS X x hx.he) (stageS Y y hy.he) h

-- all levels along A.REST toStop carry
noncomputable def climbH (i j:ℕ) (x:Stud (f i) F):Stud (f j) F:= if h:i=j then h ▸ x else if _h:i<j then climbH (i+1) j (retract A i x) else 0
termination_by j-i
-- arg order? A omitted?
lemma same (x:Stud (f i) F) : climbH A i i x=x:=by rw [climbH]; simp
lemma next (x:Stud (f i) F)(h:i<j): climbH A i j x= climbH A (i+1) j (retract A i x):=by rw [climbH,dif_neg h.ne,dif_pos h]
lemma climbs (x:Stud (f i) F)(hp:Stays x)(h:i≤ j): Stays (climbH A i j x):=by
   induction h using Nat.decreasingInduction with
   | self=>rw [same]; exact hp
   | of_succ k hk ih=>rw [Lyre.next _ x hk]; exact ih _ (retractS _ x hp)
lemma steep (x:Stud (f i) F)(q:Bool)(hp:Stays x)(hv:∀ V,Grass.Hom q (x V))(h:i≤j) : ∀ V,Grass.Hom q (climbH A i j x V):=by
    induction h using Nat.decreasingInduction with
    | self=> rw [same]; exact hv
    | of_succ k hk ih=> rw [Lyre.next _ x hk]; exact ih _ (retractS A x hp) (wrought A q x hv hp) -- order?

lemma soarL (x:Stud (f i) F)(hp:Stays x)(h:i≤ j)(Y: Insertion (f j) F)(ht:∀ k, i≤k→ k<j→ A.w k≠0): joint (x * ⇑(S.toStop R A.β A.w j i Y))= S.multiplier R A.w i j F * joint (climbH A i j x * ⇑Y):=by
    induction h using Nat.decreasingInduction with
    | self=> rw [Scheme.entrance,same]; simp [Scheme.multiplier]
    | of_succ k hk ih=> rw [Scheme.next S R A.β A.w hk Y, Scheme.nextMultiplier S R A.w hk,Lyre.next A _ hk]; let z:= S.toStop R A.β A.w j (k+1) Y; let u:=retract A k x
                        have h':joint (u * ⇑z)= _:= ih _ (retractS A x hp) (fun j hj hy=> ht j (by omega) hy)
                        change joint (x* transfer _ _ _ _ _ _)=_*_*_; rw [echo_left _ _ (S.admissible k) (ht k le_rfl hk) x (⇑z) hp (stays z.continuous)]; change _*joint (u*⇑z)=_; rw [h',mul_assoc]
end YM.Massive.Lyre
#print axioms YM.Massive.Lyre.wrought
#print axioms YM.Massive.Lyre.soarL
#print axioms YM.Massive.Lyre.steep
