import YM.Eole.Aire
/-! Sector exchange in the replica polynomial. Use ordered factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Eole
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew Function
open Lattice Wilson Creek Lat Kit NormedSpace RG Cove Filter Run
open Loom Fleet MeasureTheory Ribbon Cupola Plate Ruby
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J A B:Type}[Fintype I][Fintype J][Fintype A][Fintype B]
open Quills
open Further.ShellBirth49.Fusing Collide
variable {E K:Type} {c:Side}
local notation "N"=> E⊕K
-- nodes indexed full exponent E and fully decomposed forced.
open QCD.GasP QCD.Struck
variable (W:Bloc I J) (g:E⊕K→ Finset I) (Y:K→Hat c)
open Sway OrbitG Bay Strut Push.Local Push.AbsoluteSums Ursell Gas Graph Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
local notation "κ"=> Keys c 6
variable (q:I→ Bool) {P:BudgetPoint} {v α b t:ℝ}
open Further.ShellBirth49.Fusing Collide
variable (o:I→Site c)(p:J→Site c)
-- E raw footprint and common extensions
local notation "M"=> Patio ((Keys c 6)⊕Spine I)
local notation "Mt"=> Patio ((Keys c 6)⊕Spine J)
local notation "λt"=>W.flag q
variable (old:E→Support c)(a:E⊕K→Support c)(f:E⊕K→ Grid c→ Patio ((Keys c 6)⊕Spine I))(z:E⊕K→ℝ)
local notation "P₀"=> Grid c
set_option quotPrecheck false
local notation "T"=>P.threshold
local notation "A'"=>day f
local notation "H'"=>night old f T
local notation "S'"=> Support c
include W
variable (h:Setting W g Y q o p old a f z P t)
include h
open ConnectedActivityE6 Blaze King
local notation "L"=> Cand W g Y
local notation "G"=> Hard W g Y
local notation "Jr"=>journal W g q f
local notation "μ"=> lunarZ W g q old f
local notation "lπ"=> glowT W g
local notation "ξ"=> Stitch.Tablet.credits
local notation "Q"=> P.order
local notation "w0"=> wag
local notation "ω" i:arg=> payU (shore a i) (∏ j∈i,heightE P.order z j) P
variable (hv:0<t)
include hv
set_option maxHeartbeats 900000 in
lemma haloG (i:Cand W g Y)(r:Site c)(hk:r∈shore a i.val): Sight (shore a i.val) r 2 P t (pluck (Keys c 6) (burst (W.flag q) (glowT W g i.val))∘ journal W g q f i.val) (payU (shore a i.val) (∏ j ∈ i.val,heightE P.order z j) P):=by
     let s:=i.val; let y:=glowT W g s; let Z:=∏ j∈s,f j; let V:=shore a s; let w:=wag V P.B; let W':=1+(w:ℝ); have hR :1 ≤ W':=le_add_of_nonneg_right (by positivity); have hp₁:=zero_le_one.trans hR; let F:=Bloc.lane κ q W y; let G':=F.restrictScalars ℝ; let H:= pluck κ (burst λt y); let x:=H ∘ journal W g q f s
     have hZ (U:Grid c) :Z U=∏ j∈s,f j U:=Finset.prod_apply ..
     have hX : journal W g q f s=G' ∘ Z:=funext fun j=>congr_arg F (hZ j).symm; have hK:0 ≤ ∏ j∈s,z j:=prod_nonneg fun j _=>positiveZ W g Y q o p old a f z h hv j
     let Ee:= W'^P.power; let t':=1+(s.card:ℝ)* Ee; have hz:1≤ Ee:=one_le_pow₀ hR; have ht: t' ≤ (2:ℝ)^s.card * Ee := by
          have hp(k:ℕ): 1+(k:ℝ)≤(2:ℝ)^k:=by induction k with|zero=>simp|succ z ih=>push_cast; rw [pow_succ]; linarith [Nat.cast_nonneg (α:=ℝ) z]
          exact (add_le_add_left hz ((s.card:ℝ)*Ee)).trans ((le_of_eq (by ring : Ee+(s.card:ℝ)* Ee=(1+(s.card:ℝ))* Ee)).trans (mul_le_mul_of_nonneg_right (hp _) (zero_le_one.trans hz))) -- ann order
     have hx'(U:Grid c) : x U ∈ Creek.region (limits V):= (litter W g Y q o p old a f z h s i.2.1.2.1 U).2 _
     have hr0:= moodU W g Y q o p old a f z h i; have hX0 (j':Grid c)(hp:Healthy T V j'):= saturn W g Y q o p old a f z h hv i j' hp r hk s (Subset.refl s)
     change Sight V r 2 P t x _; refine ⟨fun X₀ Y' hH=> congr_arg H (hr0 X₀ Y' hH),hx',fun U hV=> ?_,fun U hV l hl hL=> ?_,H.measurable.comp (measurableJ W g Y q o p old a f z h s),?_⟩
     · unfold x; rw[hX]; exact (H.restrictScalars ℝ).contDiff.contDiffAt.comp _ (G'.contDiff.contDiffAt.comp _ (hX0 U hV).smooth)
     · let Gd:=leftDerivs Z l U; have hs:= hX0 U hV; let k:=(G') Gd; let f0:=leftDerivs x l U
       have hx0(j:Grid c):Polite q (W.plant y) (Z j):=by rw[hZ]; exact (show W.plant y=_ from (show mural W g s from i.2.1.2.1)).symm ▸ paint_packets g q (day f j) (fun k=>(h.price k j).1) s
       have hh:Polite q (W.plant y) Gd:=noble q _ _ hx0 U hs.smooth _ hl
       have hP:f0=pluck κ (burst λt y) k:=by unfold f0 x; rw[hX]; exact (left_linear (H.restrictScalars ℝ) l (G'.contDiff.contDiffAt.comp _ hs.smooth) hl).trans (congr_arg H (left_linear G' l hs.smooth hl))
       have he: load (fun _=>t) f0= ξ t Gd:=by rw[hP]; exact (Stitch.Tablet.polite_bill _ _ (Bloc.overlay κ q W _ Gd) hv).symm.trans (Bloc.value_norm q W _ hv _ hh)
       have hw' : t'^l.length ≤ ((2:ℝ)^s.card * Ee)^P.order:=by
          have hp:1≤ t':= le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hz)); exact (pow_le_pow_right₀ hp hl).trans (pow_le_pow_left₀ (zero_le_one.trans hp) ht _)
       have hf0:f0∈Creek.region (limits V):=Lyre.stays_left ((Creek.region (limits (F:=6) V)).toSubmodule.restrictScalars ℝ) x hx' l U; apply le_trans (rangeView r _ 2 hv V hf0 hk (B:=P.B)); rw[he]; exact (mul_le_mul_of_nonneg_left ((hs.paid _ hl hL).trans (mul_le_mul_of_nonneg_left hw' hK)) (show 0 ≤ W'^2 from sq_nonneg _)).trans_eq (by change W'^2 * ((∏ j∈s,z j)*_) = W'^(_)*(∏ j∈s,heightE _ z j); unfold Ee heightE; rw[prod_mul_distrib,prod_const]; ring)
     apply mul_nonneg (pow_nonneg hp₁ _); exact prod_nonneg fun j _=> mul_nonneg (pow_nonneg (by norm_num : 0≤(2:ℝ)) _) (positiveZ W g Y q o p old a f z h hv j)
end YM.MassiveQCD.Sample.Eole
#print axioms YM.MassiveQCD.Sample.Eole.haloG
