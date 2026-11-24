import YM.Pollen.Amber
import YM.Clays.Benny
import YM.Clays.Acer
import YM.Bister.Body
import YM.Pollen.Oak
import YM.Helio.Ribbons
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Basal
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k:ℕ}{I D:Type}[Fintype I]{a t b w x v θ m:ℝ}
variable (o:I→Site c) {U:BudgetPoint}
variable (V: I→Grid c→ Fields c N→L[ℂ]Fields c N) (H:∀ i,Suit (o i) U a (V i)) (d:I→ℂ) (s:List I)
local notation "P"=> Patio (Keys c N⊕Spine I)
local notation "S"=>Support c
local notation "q"=> traceI I
set_option quotPrecheck false
local notation "Φ" X:arg=> effU (fun k=> V k X) (fun k=> (H k).bean X) d
local notation "Ω" X:arg=> actU (fun k=> V k X) (fun k=> (H k).bean X) d
include H
open Stretch
local notation "μ₀"=> ample N I
variable (F :Patron.Rail c (ample N I) D)
local notation "L"=> withdraw N o t
local notation "R"=> banknote N o t
local notation "qT" i:arg=> (F.addr i).place
omit H
local notation "K"=> furtherK o V H d s F t
local notation "Z"=> roofV o s F
local notation "E"=> MotK o s F
local notation "ρμ" j:arg=>beamFee U.B j
include H
variable (h: Wage.Tip N o (traceI I) F U t b v)(ht:0 < t)
include h ht
variable (htV:1 ≤ v)(hu:1 ≤ t)(hb:0 ≤ b)(hr:s.Nodup)
include hr
variable {T Q ε ρ:ℝ}
local notation "gΦ" i:arg=> s.filter (fun j=>j∈ (i:Finset I))
set_option maxHeartbeats 860000 in
lemma budgetK (A:ℝ)(Ft:ℕ) (hF: Fires o Ft)(hx:0 < ε)(hp:0 ≤ w)(hh:w+2*ε ≤ b)(hZ:0 ≤a)(hξ:0 ≤ x)(hW:∀ i,‖d i‖ ≤ x) (hv:A≥1)(hT:1 ≤ T)(hX:A*T≤ v)(hM:hullP U.B Ft*(Real.exp w*(a*x))≤ ε)(hR:A⁻¹+beamFee U.B Ft (a*x) w ε*A⁻¹ ≤ ρ) : Kites.Quits (K) U.B ρ T w t:=by
    obtain ⟨g,hg,hG⟩:= h.tilt.sold.cost; have hy(i):0≤g i:=(norm_nonneg _).trans (hG i 1); let l:= QCD.GasP.taxed (Ruby.oriD F) g T; let Z':=A⁻¹; let W:=beamFee U.B Ft (a*x) w ε
    have hy:0 ≤ T:=zero_le_one.trans hT; have h_v:0 ≤ v:= (mul_nonneg (zero_le_one.trans hv) hy).trans hX; have hQ:0<A:=zero_lt_one.trans_le hv; have h':Ac.Hit (Ruby.home F) U.B l b Z':=by
           intro j; have hz:= (Ruby.scopes (A:=0) F hQ h_v (‹∀ i:D,0 ≤ g i›) hg hT (by simpa using hX) hv j); have hz(i:D): metal F (0:ℝ) i=1:=by simp [metal]
           convert (show SumBudget _ _ from (Ruby.scopes (A:=0) F hQ h_v (‹∀ i:D,0≤g i›) hg hT (by simpa using hX) hv j)) using 1; funext i; unfold l; simp [hz] -- check priority
    have hl(i:D):0 ≤ l i:= mul_nonneg (pow_nonneg hy _) (‹∀ i:D,0≤g i› i)
    let R':=a*x; have hp':0 ≤R':=mul_nonneg hZ hξ; let F'(i:E):=R'^i.2.val.card * g i.1
    have h0:A⁻¹≥0:=by positivity
    have hq: Ac.Hit (fun i:E=>Ruby.home (K) (Sum.inr i)) U.B (fun i:E=> R'^i.2.val.card*l i.1) w (W*Z'):=woodPays o (Ruby.home F) (ridingK o s F) (fun i j hi=> (tightK o s F i ⟨j,hi⟩).2) U.B Ft U.B_pos _ hp' l hl h' hp ε hx hF hM hh -- order.
    refine ⟨Sum.elim g F',fun j=> ?_,?_⟩; swap
    · rintro (i|i) X; · exact hG i X
      let y:=L (F.warp i.1 X); let z:=gΦ i.snd.val; let Q:=(Φ X) z; change ‖token c μ₀ t (R (Q y))‖ ≤ _; rw[from_full o ht]; have hm:Stitch.Tablet.credits t y≤g i.1:=by rw [← from_full o ht, show R _=F.warp i.1 X from (h.fits ..).spark]; exact hG _ X
      rw[show Sum.elim g F' (Sum.inr i)= R'^z.length *g i.1 from ?_]; swap
      · rw [show z.length=i.snd.val.card from payScope s hr _ (tightK o s F i.fst i.snd).1]; rfl
      exact (spendsU o V H d z X y ht hZ hξ hW).trans (mul_le_mul_of_nonneg_left hm (pow_nonneg hp' _))
    let k(i:D⊕E):= (K).addr i; let p:= Sum.elim g F'; let f(i:D⊕E):= if j∈(k i).place then (T^(k i).inv.card*p i)*Real.exp (w*coverNumber U.B (k i).place) else 0
    have h₁: SumBudget (f ∘ Sum.inl) Z':=by
          refine budget_mono (h' j) (fun i=> ite_nonneg (mul_nonneg (hl i) (Real.exp_pos _).le) le_rfl) fun i=>?_
          change f (.inl i)≤_; unfold f; by_cases he:j∈ Ruby.home F i; · rw [if_pos he,if_pos (show j∈(k (Sum.inl i)).place from he)]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith : w ≤ b) (Nat.cast_nonneg _))) (hl _)
          rw [if_neg he,if_neg (show j∉(k (Sum.inl i)).place from he)]
    have h₂ : SumBudget (f ∘ Sum.inr) (W*Z'):=by
          convert hq j using 1; funext i; unfold f k; change (if j∈ Ruby.home (K) (.inr i) then _ else _) = ite _ _ _; split; next he=>
                                                                  change T^((F.addr i.fst).inv.card)*( R'^i.2.val.card*g i.1)*_= R'^i.2.val.card*(T^((F.addr i.fst).inv.card)*g i.fst)*_; rw [mul_left_comm (T^_)]; rfl -- mul issue
          next => rfl
    have ht: SumBudget f (Z'+W*Z'):=by
           have he:=h₁.2.1.hasSum.sum (f:=f) h₂.2.1.hasSum
           exact ⟨fun i=>by rcases i with i|i; exact h₁.1 _; exact h₂.1 _,he.summable,he.tsum_eq.trans_le (add_le_add h₁.2.2 h₂.2.2)⟩
    exact budget_loosen ht hR
-- exact aperture expansion per F payment.
variable (ha :1 < U.B*U.B)(X:Grid c)(M:Finset I)(he:Spaced o M U.B)
local notation "Xs"=> shutter (Keys c N) M
include ha he
lemma plaque (i:D) : Xs ((Ω X) s (L (F.warp i X)))= Xs (L (F.warp i X))+ ∑ j:↥(ridingK o s F i), Xs (L ((K).warp (.inr ⟨i,j⟩) X)):=by
     let x:=L (F.warp i X); let Y:=qT i; have hy:clad (limits Y) x.val:=fun K'=>Cupola.pennied N o t K' _ Y (h.tilt.uses.role ..); let T j:= (Φ X) (gΦ j) x; have hx (j:↥(ridingK o s F i)): L ((K).warp (.inr ⟨i,j⟩) X)=T j.val:=Cupola.home N o t ht _; let y j:=Xs (T j); have hm:y ∅=Xs x:=by unfold y T; rw [show List.filter (fun j=>decide (j∈(∅:Finset I))) s=[] from by simp]; rfl
     rw [paysU _ _ d s hr, map_sum]; let Q:=s.toFinset.powerset; let L':=ridingK o s F i; simp_rw [hx]; change (∑ i∈Q,y i)=Xs x+ ∑ j:↥L',y j.val; rw [sum_coe_sort, ← add_sum_erase Q _ (mem_powerset.mpr (empty_subset _)),hm]; apply congr_arg; symm; refine sum_subset (s₁:=L') (fun j hj=>mem_erase.mpr ⟨(tightK o s F i ⟨j,hj⟩).2.1.ne_empty,mem_powerset.mpr (tightK o s F i ⟨j,hj⟩).1⟩) fun j hj hx=>?_ -- paysU arg? d named a
     obtain ⟨hQ,hB⟩:= mem_erase.mp hj; have hB:=mem_powerset.mp hB; have hv:= viewingP s j hB; by_cases hr': j⊆ M; swap
     · exact shutU o V H d _ X M x (fun e=>hr' (hv ▸ e))
     obtain ⟨p,hp,hw⟩:= Finset.not_subset.mp (show ¬ j⊆ barn o Y from fun hz=>hx (mem_filter.mpr ⟨mem_powerset.mpr (subset_inter hB hz), nonempty_iff_ne_empty.mpr hQ⟩)); refine Eq.trans (congr_arg (Xs) ?_) (map_zero _); exact vanishedU o V H d _ X x Y hy (fun _ hh _ hh' h=> he _ (hr' (hv ▸ hh)) _ (hr' (hv ▸ hh')) h) ha (hr.filter _) (List.mem_toFinset.mp (hv.symm ▸ hp)) (fun e=>hw ((inside ..).2 e))
end YM.MassiveQCD.Sample.Basal
#print axioms YM.MassiveQCD.Sample.Basal.budgetK
#print axioms YM.MassiveQCD.Sample.Basal.plaque
