import YM.Gust.Zap
import YM.Gust.Malt
set_option autoImplicit false
set_option maxHeartbeats 710000
noncomputable section
namespace YM.Massive.Gust
open Function Filter Set MeasureTheory Measure Complex Analysis Table Work.A01 Outer Tarn Tarn.Choir
open scoped Topology ContDiff BigOperators NNReal ENNReal InnerProductSpace Classical
variable {m : ℕ}
lemma sands (T: Choir)(J:Axis→ Axis→ T.W) (C: Safe T J) (K : Ortho.Skew)
    (χ : Fin (m+1)→E4→ℝ) (x : Points (m+1)) (w : Quarry x χ) (q : Fin (m+1)→T.W) (y : E4) :
    vigor x q J (wash K χ) y= ∑ i,∑ a,∑ b,termG J (χ i) (Outer.roll K) x q a b y := by
  let A i a b := (χ i y * D (basis a) (comps b (roll K)) y) • phot J q x a b y
  have ht (i) : ∑ a, ∑ b, A i a b=0 := by
    have he a b : A i a b= -A i b a := by
      unfold A; rw [show D (basis a) (comps b (roll K)) y=_ from roll_k K a b y, mul_neg,neg_smul]
      unfold phot; rw [C.symmetric a b]
    let z := ∑ a,∑ b,A i a b
    have hh : z= -z := calc
      _ = ∑ a,∑ b, -A i b a := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => he a b
      _ = -z := by rw [Finset.sum_comm]; simp_rw [Finset.sum_neg_distrib]; rfl
    have hf : 2*z=0 := by
      rw [two_mul]; conv_lhs => lhs; rw [hh]
      exact neg_add_cancel _
    exact (mul_eq_zero.mp hf).resolve_left (by norm_num)
  have he a b : stream x q J (wash K χ) a b y= ∑ i, (termG J (χ i) (Outer.roll K) x q a b y+A i a b) := by
    unfold stream; rw [wash_d K χ (fun i => (w i).1),Finset.sum_smul]; apply Finset.sum_congr rfl; intro i hi
    rw [add_smul]; rfl
  unfold vigor; simp_rw [he]
  rw [show (∑ a : Axis, ∑ b : Axis, ∑ i, (termG J (χ i) (Outer.roll K) x q a b y+A i a b))=∑ i,∑ a,∑ b,(termG J (χ i) (Outer.roll K) x q a b y+A i a b) by
    rw [Finset.sum_comm];
    rw [Finset.sum_comm (s:=Finset.univ) (f:=fun i a => ∑ b,(termG J (χ i) (Outer.roll K) x q a b y+A i a b))]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; exact Finset.sum_comm ]
  refine Finset.sum_congr rfl fun i _ => ?_; simp_rw [Finset.sum_add_distrib,ht,add_zero]

variable {K: Choir}{C:Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf:Foil P K T)
open UV Kind Tarn.ChargeQ
variable (A:Axis×Axis→K.W)(hA:Persona T A) (J:Axle K (fun a b=>A (a,b)))(U:Vane J)(x:Points (m+1))(hx:x∈conf _)(v:Fin (m+1)→K.W)(s:Fin (m+1)→Bool)(hp:∀ i,v i∈ Col T (s i))
local notation "Jt"=> fun a b=>A (a,b)
noncomputable abbrev valor (g:Ortho.Skew):= ∑ i,K.total _ x (update v i (swirl K A J U g (x i) (v i)))
include hp hx hf hA hK
lemma freeness (g:Ortho.Skew)(F:Axis→E4→ℝ)(hF:∀ b,ContDiff ℝ ∞ (F b))(hl:∀ b,HasCompactSupport (F b))(hk:∀ b i,F b=ᶠ[𝓝 (x i)] comps b (roll g)):
        valor A J U x v g= -(∫ y,vigor x v (Jt) F y):=by
       obtain ⟨χ,hχ⟩:=quarry x hx; let u:= wash g χ; let Z:= F-u
       have hs b: ContDiff ℝ ∞ (u b):= wash_s _ _ _ fun i=> (hχ i).1
       have hh b: ContDiff ℝ ∞ (Z b):= ContDiff.sub (hF b) (hs b)
       have hu b:HasCompactSupport (Z b):= HasCompactSupport.sub (hl b) (wash_short _ _ _ fun i=>(hχ i).2.1)
       have hw (b i): x i∉ tsupport (Z b):= notMem_tsupport_iff_eventuallyEq.mpr (by have h:F b=ᶠ[𝓝 (x i)] u b:=(hk b i).trans (wash_home x χ g hχ i b).symm; filter_upwards [h] with y h; change F b y-u b y=0; rw [h,sub_self])
       have hT: Safe K (Jt):=⟨hA.tense.sym,soma A hA⟩
       obtain ⟨hB,hZ⟩:= Gust.paid_zero hK _ hT x hx v Z hh hu hw
       have he(y): vigor x v (Jt) F y=vigor x v (Jt) Z y+vigor x v (Jt) u y:=by
            have h (a b:Axis): stream x v (Jt) F a b y= stream x v (Jt) Z a b y+stream x v (Jt) u a b y:=by
                 unfold stream; rw [←add_smul]; congr 1; unfold Z D; rw [Pi.sub_apply,fderiv_sub (show DifferentiableAt ℝ _ y from (hF b).differentiable (by simp) y) ((hs b).differentiable (by simp) y),_root_.sub_apply, sub_add_cancel]
            simp_rw[vigor,h,Finset.sum_add_distrib]
       let H:=arc_cost hK hf A hA J U x hx v g s hp; have hC(i):= H i _ (hχ i)
       have hV: Integrable (vigor x v (Jt) u):=by rw[funext (Gust.sands K (Jt) hT g χ x hχ v)]; exact integrable_finsetSum _ fun i _=> integrable_finsetSum _ fun a _=> integrable_finsetSum _ fun b _=>(hC i).1 a b
       simp_rw[he, integral_add hB hV,hZ,zero_add]; simp_rw [show ∀ y,vigor x v (Jt) u y=_ from sands K (Jt) hT g χ x hχ v]
       rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _ fun a _=> integrable_finsetSum _ fun b _=> (hC i).1 a b),← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [← (hC i).2, integral_finsetSum _ (fun a _=>integrable_finsetSum _ fun b _=> (hC i).1 a b)]; congr 1; apply Finset.sum_congr rfl; intro a _; rw [integral_finsetSum _ (fun b _=> (hC i).1 a b)]
lemma quake(a b l:Axis)(h:a≠b)(hl:Ward.onLine l x): valor A J U x v (Ortho.plane b a)=0:=by
       obtain ⟨hB,hX⟩:= windWard hK hf a b l A hA v s hx hl hp h; obtain ⟨hP,hY⟩:=windWard hK hf b a l A hA v s hx hl hp h.symm
       let F:= valor A J U x v (Ortho.plane b a); have hu: Budget (-1) (fun _=>F):=by
            refine ((hX.sub hY).neg).same ?_
            filter_upwards [hB,hP,eventually_all.mpr fun i=>eventually_all.mpr fun j=> vane_home (x j) a b l i h] with t hp1 hp2 hz; change -( _ - _ )= F; unfold F; rw [freeness hK hf A hA J U x hx v s hp _ (vane a b l t) (fun _=>vane_s ..) (fun _=>vane_k ..) hz]; simp_rw [gustL_river x v (Jt) hA.tense.sym a b l h t]; rw [integral_sub hp1 hp2]
       exact tendsto_nhds_unique tendsto_const_nhds (hu.limits (by norm_num))
end YM.Massive.Gust
#print axioms YM.Massive.Gust.quake
