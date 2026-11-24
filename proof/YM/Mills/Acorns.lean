import YM.Mills.Earner
/-! # operator-return estimate on whole log, still credited from genuine rung. Retain decay for dropping *individual* costly visits. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}
local notation "I"=> Pipe.Clump S ι
local notation "C'"=>Coat T
variable (Y:Fleet H ι N)
set_option quotPrecheck false
open Art Blaze Polar Shield Frond
open Grass Cove Lat GasP Filter Ursell Graph Jets.Touch
set_option quotPrecheck false
local notation "B"=>radiusB τ
variable (θ :ℝ) (κ :ι→ℝ)
-- on actual wallets; boosted Hit on each stage.Op
local notation "uQ"=> Glow.simple Q L μ C θ R.beta τ
local notation "bQ"=> Glow.billsV Q L μ C θ R.beta τ
local notation "φ"=> lantern L τ
private lemma inkP {w₁ w₂:Costs}(hw:w₁.extraSeed=w₂.extraSeed)(u:I):∀ i∈u,Y.shellF.inks w₁ κ i=Y.shellF.inks w₂ κ i:=by
   rintro ((i|i)|i) _; · exact congr_arg₂ (·*·) hw rfl
   · rfl
   rfl
-- unified piece multiplier without requiring same F opt relation. It is scalar /plot regardless allot.
variable {a:ℝ}
def pollen (κ:ι→ℝ)(ν:ℝ) (i:I) := ∏ j∈i,Sum.elim (fun _=>ν) κ j
def stipendP (u:ℝ)(i:Clusters Y.Bright): ℝ:= ∏ j,pollen κ u (i.2 j).val
lemma pollen_one (hu:1≤a)(hk:∀ i,1 ≤ κ i)(p:I):1 ≤ pollen κ a p:=Finset.one_le_prod fun i _=>by rcases i with i|i; exact hu; exact hk _
lemma stipendP_one (hu:1≤a)(hk:∀ i,1 ≤ κ i)(p:Clusters Y.Bright): 1 ≤ Y.stipendP κ a p:= one_le_prod fun i _=> pollen_one κ hu hk _
variable {w v : Reserve S→ ι →ℝ} {a:ℝ}
lemma earnings (ht:Y.Leaps w uQ (fun _=>0) a)(hv:∀ k,Ac.Hit Y.ground B (v k) Q.relative (Glow.levelX L θ τ)) (hz:∀ k,0 ≤ v k) (hh:∀ k i,w k i*κ i≤v k i) (hk:∀ i,1 ≤ κ i)(h:S.patch.L=L)(hf:1≤φ)(hQ:(bQ).Buy L Q.halo (radiusB τ)) : Ac.Hit (Y.fullA) B (fun i=>if Ac.Spark (Y.shellF).gP i then Y.grass w uQ i * pollen κ φ i else 0) (bQ).exponent (apple bQ):=by
   let ν := φ
   let f (k:Reserve S) i:=if Ac.Spark (Y.shellF).gP i then Y.guess uQ (w k) i * pollen κ ν i else 0
   have hα(k:Reserve S):Ac.Hit Y.fullA B (f k) (bQ).exponent (apple bQ):=by
      let C₁:= Y.suitcase (allot k); let g:= C₁.ideal θ (v k); have hψ:0 ≤ (v k):= by apply hz
      obtain ⟨hr,hp⟩:= C₁.earnest h hψ hf hQ (hv k)
      have h₀(j):0≤ C₁.inks bQ (fun _=>0) j:= ((C₁.digits (ht k).1 j).2) -- inks same rfl
      have hs:= C₁.grassbud bQ _ g hr (h ▸ hQ) hp h₀
      intro i; refine budget_mono (hs i) (fun j=>?_) (fun j=>?_)
      · split; swap; · exact le_rfl
        unfold f; split; · exact mul_nonneg (mul_nonneg (prod_nonneg fun i _=>(C₁.digits (ht k).1 i).1) (zero_le_one.trans (pollen_one κ hf hk _))) (Real.exp_pos _).le
        rw [zero_mul]
      split; next hi=>
         rw [if_pos (show i∈ C₁.full j from hi)]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; unfold f; split; next hk₀=>
            dsimp only; rw [if_pos (show Ac.Spark C₁.gP j from hk₀)]; unfold guess pollen; rw [← prod_mul_distrib]; apply Finset.prod_le_prod
            · rintro (i|i) _; exact mul_nonneg (C₁.digits (ht k).1 _).1 (zero_le_one.trans hf); exact mul_nonneg (C₁.digits (ht k).1 _).1 (zero_le_one.trans (hk _))
            intro i _; exact C₁.luminous (θ:=θ) (hh k) i
         next hk₀=> dsimp only; rw [if_neg (show ¬Ac.Spark C₁.gP j from hk₀)]
      next _=>exact (hs i).1 _
   intro x
   letI : Nonempty (Tree.Forest S.ratio):= Tree.select S.ratio S.patch.odd_side
   let V (i:Reserve S) (j:I):=if x∈Y.fullA j then f i j * currency B (bQ).exponent (Y.fullA j) else 0
   let Yc:=apple bQ; have hx k:SumBudget (V k) Yc:=hα k x
   let n:ℝ:= Fintype.card (Reserve S)
   have hs:0<n:=Nat.cast_pos.mpr Fintype.card_pos
   let g i := if Ac.Spark (Y.shellF).gP i then Y.grass w uQ i*pollen κ ν i else 0
   have hH j:(if x∈ Y.fullA j then g j * currency B (bQ).exponent (Y.fullA j) else 0)= n⁻¹ *∑ i:Reserve S, V i j :=by
       unfold V f g grass choiceS currency; split_ifs with he hf
       · dsimp only; rw [← sum_mul,←sum_mul,smul_eq_mul]; unfold n; ring
       · rw [zero_mul,sum_const_zero,mul_zero]
       rw [sum_const_zero,mul_zero]
   change SumBudget (fun j=> if x ∈ Y.fullA j then g j * currency _ _ _ else 0) Yc
   convert! budget_scale (inv_nonneg.mpr hs.le) (budget_over (univ:Finset (Reserve S)) V (fun _=>Yc) (fun i _=>hx i)) using 1; apply funext hH
   rw [sum_const,nsmul_eq_mul,card_univ,show (Fintype.card (Reserve S):ℝ)=n from rfl]; field_simp
variable {α:ℝ}{χ:Chi}
lemma rim (ht:Y.Leaps w uQ (fun _=>0) a)(hv: Ac.Hit (Y.fullA) B (fun i=>if Ac.Spark (Y.shellF).gP i then Y.grass w uQ i * pollen κ φ i else 0) (bQ).exponent (apple bQ))(hα:Corner Q (radiusB τ) bQ α)(hk:∀ i,1 ≤ κ i)(hf:1≤φ) :
   let g i:= Y.grass w uQ (i:Y.Bright).val; let X i:= coversP Y.lightF g i; let D i := Y.stipendP κ φ i
   (∀ i:Clusters Y.Bright,0 ≤ X i) ∧ (∀ i U, ‖token c N a (Y.honest χ U i)‖ ≤ X i ∨ ¬ Y.Famous) ∧ Ac.Hit (seatP Y.lightF) B (fun i=> D i*X i) (α+1) 1:=by
    intro g X D
    let p (i:Y.Bright):=pollen κ φ i.val; let α' i := g i * p i
    have hp i:0 ≤ p i:=zero_le_one.trans (pollen_one κ hf hk _)
    have hQ i:0 ≤ α' i:=mul_nonneg (Y.nonC ht i.val) (hp i)
    let γ:=apple bQ
    have hh: Ready Y.lightF (radiusB τ) α' (α+1) γ 1 (1/2):=by
       refine ⟨hα.directs,zero_lt_one,hα.adds,(by norm_num),hQ,fun j=>?_⟩
       have he':= budget_pull (fun j:Y.Bright=> j.val) Subtype.val_injective (hv j)
       refine budget_mono he' (fun i=>?_) (fun i=>?_)
       · split; exact mul_nonneg (hQ _) (Real.exp_pos _).le; exact le_rfl
       split; next hi=>
           rw [if_pos (show j ∈ Y.fullA i.val from hi )]; dsimp only; rw [if_pos i.2.1.2.1]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hα.used (Nat.cast_nonneg _))) (hQ _)
       next _=>exact he'.1 _
    let t:= coversP Y.lightF α'; have hY:D*X=t:=by
        funext i; change _*_=coversP _ _ _; unfold D X coversP; unfold clusters; -- inspect
        simp only [α',prod_mul_distrib]; unfold stipendP p; ring
    refine ⟨fun i=> clusters_nonneg (blocked Y.lightF) (fun i=> Y.nonC ht i.val) _,?_,?_⟩
    · intro i U; by_cases hg:Y.Famous; swap; · exact Or.inr hg
      have hy: wearK c N a (Y.honest χ U i)= termP (blocked Y.lightF) (wearK c N a ∘ Y.dawnV χ U) i:=by rw [phoenix Y χ U hg]; exact transportTerm Y _ _ _ _
      have hw: ‖token c N a (Y.honest χ U i)‖=‖termP (blocked Y.lightF) (wearK c N a ∘ Y.dawnV χ U) i‖:=(skill a _).trans (congr_arg _ hy)
      exact Or.inl (hw.trans_le (term_bill (g:=g) (fun i=> ((skill a _) ▸ Y.localP ht χ U i.val)) _))
    have hx: Ac.Hit (seatP Y.lightF) B t (α+1) (γ*(1-(1/2:ℝ))⁻¹):=by
       have h₁ i : (Y.lightF i).Nonempty:= i.2.1.1
       intro i; simpa only [coversP,seatP,t,currency,Nat.zero_le,true_and,pow_zero,mul_one] using! log_hit_tail (blocked Y.lightF) Y.lightF (radiusB τ) (literal_test Y.lightF h₁) hh (add_nonneg hα.exp zero_le_one) 0 i
    change Ac.Hit _ _ (D*X) _ _; rw [hY]; exact fun i=> budget_loosen (hx i) hα.success
end YM.QCD.Loom.Fleet
#print axioms YM.QCD.Loom.Fleet.earnings
#print axioms YM.QCD.Loom.Fleet.rim
