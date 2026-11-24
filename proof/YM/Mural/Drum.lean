import YM.Mural.Mast
import YM.Mills.Glow
import YM.Mills.OrientL
/-! # enhanced billing of SEMINORM, retaining Root budget per publication. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Mural
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Pipe Cove Leaf Lat PhysicalNext.Repeat.Greenbelt Loom Loom.Fleet
open Grass Cove Lat GasP Filter Ursell Graph Jets.Touch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ:Type}{N n:ℕ}
local notation "I"=> Pipe.Clump S ι
variable (Y:Fleet H ι N) (X:Finset (Keys c N))
set_option quotPrecheck false
variable {x z θ t:ℝ}
noncomputable def paidM (z:ℝ)(n:ℕ)(v:ℝ): EvenA c N →L[ℝ] Grass.Alg (Keys c N):= LinearMap.toContinuousLinearMap (((changeVars (Matrix.diagonal (fun _:Keys c N => (v:ℂ)))).toLinearMap.comp ((surge X z n).comp (Cove.light _).toLinearMap)).restrictScalars ℝ)
lemma payment (y:EvenA c N) : ‖paidM X z n x y‖= repay X z n (fun _=>x) (light _ y):=rfl
lemma light_minor (hX:0<x)(hz:1≤z) (y:EvenA c N): ‖token c N x y‖ ≤‖paidM X z n x y‖:= minor X z n (fun _=>x) hz (fun _=>hX) _
lemma stake_pro (hX:0<x)(hz:1 ≤z)(s:Finset ι)(p:ι→EvenA c N): ‖paidM X z n x (∏ i∈s,p i)‖ ≤∏ i∈s, ‖paidM X z n x (p i)‖:=Mural.funded _ _ _ _ hz (fun _=>hX) s p _ (fun _ _=>le_rfl)
structure Vigil (F: Tree.Forest S.ratio)(x:ι→Site c)(b:ι→ℝ)(z:ℝ)(n:ℕ)(v a:ℝ)(p:Finset ι)(i j:ℕ):Prop where
 grow:0 ≤a
 rise k:0≤ b k
 seat y: (p.filter fun j=>x j=y).card ≤ j
 rare j :∀ Z:Coat T F,Z.x=τ→Z.width=o.K→ Z.manifest → ∀ w:Air f su,b j < ‖paidM X z n v (Y.coming j Z w)‖→j∈p ∧ ∃ k∈Y.ground j,k∈Z.seeds.place ∧ separation k (x j) ≤ i
 cover j :∀ Z:Coat T F,Z.x=τ→Z.width=o.K→ Z.manifest→ ∀ w:Air f su, ‖paidM X z n v (Y.coming j Z w)‖ ≤ Real.exp a*b j
variable {J:ι→ℝ} {Z' :ι→ Site c} {v a:ℝ}{slim:Finset ι}{i m:ℕ}
lemma sans (JH: Vigil Y X F Z' J z n v a slim i m) (hv:0<v)(hz:1 ≤z): Theft Y F Z' J v a slim i m:= ⟨JH.grow,JH.rise,JH.seat,fun j X hx hw h Z hzX=>JH.rare j _ hx hw h Z (hzX.trans_le (light_minor _ hv hz _)),fun j X hx hw h Z=> (light_minor _ hv hz _).trans (JH.cover j X hx hw h Z)⟩
lemma posting {V:Fleet H κ N}{f:κ→Site c}{g:κ→ℝ}{r:Finset κ}{w h:ℕ} (hs:Vigil Y X F Z' J z n v a slim i m) (hc: Vigil V X F f g z n v a r w h) : Vigil (united Y V) X F (Sum.elim Z' f) (Sum.elim J g) z n v a (slim.disjSum r) (max i w) (m+h):=by
   constructor
   · exact hs.grow
   · rintro (i|i); exact hs.rise i; exact hc.rise _
   · intro x; rw [show Finset.filter (fun j=> Sum.elim Z' f j=x) (slim.disjSum r)=(slim.filter fun j=>Z' j=x).disjSum (r.filter fun j=> f j=x) from ?_,card_disjSum]; exact Nat.add_le_add (hs.seat x) (hc.seat x)
     ext p; rcases p with p|p <;> simp
   · rintro (y|y) U hv hp h z hz
     · obtain ⟨hy,k,hk,he,hh⟩:= hs.rare y U hv hp h z hz; exact ⟨inl_mem_disjSum.mpr hy,k,hk,he,hh.trans (le_max_left ..)⟩
     obtain ⟨hy,k,hk,he,hh⟩:= hc.rare y U hv hp h z hz; exact ⟨inr_mem_disjSum.mpr hy,k,hk,he,hh.trans (le_max_right ..)⟩
   · rintro (x|x) Z ht hp hs' z; exact hs.cover x Z ht hp hs' z; exact hc.cover x Z ht hp hs' z
lemma refined (hv: Vigil Y X F Z' J z n v a slim i m) (hz:1 ≤z)(h:0<v): (Y.suitcase F).Merit J (a*((Animals.ballCost (i+1):ℝ)*m)) (paidM X z n v):=by
   refine ⟨hv.rise,fun s V he ht hs hb hp u=>?_⟩
   let P:= Y.suitcase F; let E:= P.sizeP s
   let W:= s.toRight; let t j:= Y.coming j V u; let S' := W.filter fun j=> J j < ‖paidM X z n v (t j)‖
   have hu j (hi:j∈ S') := hv.rare j V he ht hs u (show J j< _ from (mem_filter.mp hi).2)
   have hv' : S'.card ≤ E*Animals.ballCost (i+1)*m := P.seedPop hp S' Z' i (fun y=>
     (Finset.card_le_card (Finset.filter_subset_filter _ fun j hi=> (hu j hi).1)).trans (hv.seat y)) fun j h=>by
        obtain ⟨k,hk,hy,hw⟩:= (hu j h).2
        exact ⟨k,hy,P.leP s ((mem_filter.mp h).1) hk,hw⟩ -- fixed
   let p:= Real.exp a
   have hh:1≤p:=Real.one_le_exp hv.grow
   let f j:= ‖paidM X z n v (t j)‖
   have hy j (hi:j∈W) : f j ≤ (if j∈ S' then p else 1)*J j:=by
      by_cases hg:j∈ S'
      · rw [if_pos hg]; exact hv.cover j V he ht hs u
      rw [if_neg hg,one_mul]; exact le_of_not_gt fun hb=> hg (mem_filter.mpr ⟨hi,hb⟩)
   apply (stake_pro X h hz W t).trans; apply (prod_le_prod (fun _ _=> norm_nonneg _) hy).trans; rw [prod_mul_distrib]; change _* (∏ i∈W,J i) ≤ _*(∏ i∈W,J i)
   apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun _ _=> hv.rise _)
   rw [prod_ite]; have hb: W.filter (fun i=> i∈S')=S':= by ext x; rw [mem_filter,and_iff_right_of_imp (fun h=>(filter_subset _ _) h)]
   rw [hb,prod_const,prod_const_one,mul_one]; apply le_trans (pow_le_pow_right₀ hh hv'); unfold p; rw [← Real.exp_nat_mul]; apply le_of_eq; push_cast; congr 1; unfold E; ring
variable {t h k:ℝ}{B:Costs}{w: Reserve S→ι→ℝ}
local notation "C!"=>paidM X z n k
structure Blast (z k:ℝ)(n:ℕ)(w:Reserve S→ι→ℝ)(b:Costs) :Prop where
   energy: Y.Leaps w b (fun _=>0) k
   price (i s V χ) : ‖paidM X z n k ((Y.suitcase (allot i)).shootsP (prism T τ χ o.K V (allot i)) s)‖ ≤ ∏ j∈s,(Y.suitcase (allot i)).dues b (w i) j
-- explicit cost. Amplitudes.Wake unstaged.
variable (hA:Blast Y X z k n w B) (h': Corner Q (radiusB τ) B a)
include hA
lemma burning (χ:Chi)(V:Grid c)(u:I): ‖C! (Y.vF u χ V)‖≤grass Y w B u:=by
    unfold grass vF choiceS; rw [map_smul,map_sum,norm_smul]; refine (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun i _=>hA.price i u V χ))) (norm_nonneg _)).trans_eq ?_
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ (Fintype.card (Reserve S):ℝ)⁻¹),smul_eq_mul]; rfl
open Art Blaze
include h'
local notation "r"=> radiusB τ
lemma wagesG (χ:Chi)(hF:Y.Famous)(hb:0<k)(hz:1 ≤z): let g i:=coversP Y.lightF (fun j=> Y.grass w B j.val) i; (∀ p V, ‖C! (Y.honest χ V p)‖ ≤ g p)∧ Ac.Hit (seatP Y.lightF) r g (a+1) (apple B*(1-(1/2:ℝ))⁻¹):=by
    intro g; constructor
    · intro i V; rw [phoenix Y χ V hF]; unfold termP; -- verify def
      -- scalar vols
      unfold g coversP clusters
      simp only [map_smul,norm_smul,norm_inv, Real.norm_natCast]; rw [div_eq_inv_mul, Real.norm_eq_abs]; gcongr
      exact (stake_pro X hb hz _ _).trans (prod_le_prod (fun i _=>norm_nonneg _) (fun i _=> burning Y X hA χ V _)) -- inspect
    intro i; have hh:= hA.energy; have ht:= ceremony Y hh (add_nonneg h'.exp (by norm_num:(0:ℝ)≤1)) h'.used zero_lt_one h'.directs h'.adds (by norm_num); have h₁ x : (Y.lightF x).Nonempty:= x.2.1.1
    simpa only [coversP,GasP.seatP,g,currency,Nat.zero_le,true_and,pow_zero,mul_one] using! log_hit_tail (blocked Y.lightF) Y.lightF (radiusB τ) (literal_test Y.lightF h₁) ht (add_nonneg h'.exp zero_le_one) 0 i
end YM.QCD.Mural
#print axioms YM.QCD.Mural.wagesG
#print axioms YM.QCD.Mural.refined
