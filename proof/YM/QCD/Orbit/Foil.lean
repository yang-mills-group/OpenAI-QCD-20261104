import YM.QCD.Orbit.Hall
import YM.Next.RANK.Coordinates

/-! # assembly at zero-F. H budgets are after-L. Not repeatedly adding Wood every step
-/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 45000
namespace YM.QCD.Orbit.Birth
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine Rudder
open Precision Stationary Eyrie Run Revolve Flume Sparks Quarry YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Macrame
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {n c f : Side}{T : Type*}{j k : ℕ}{r δ b d u:ℝ}{X:Works T}
-- from fixed representations enforcing per-period Majestic (full sym all backgrounds)
lemma Vital.solozero : Vital (fun _ _=>0) :=by refine ⟨fun f=> ⟨fun k U=>by simp [aura],⟨fun i s d p _ _=>by simp [aura], fun i=>by simp [newborn,aura]⟩,fun i d _ _=>by simp,rfl,contDiffAt_const⟩, fun {f F n} L s h U=>by simp⟩
lemma Vital.add {A V:(f:Side)→Grid f → Sheet f}(h:Vital A)(hp:Vital V): Vital (A+V):=by
  refine ⟨fun n=>?_,?_⟩
  · let Q:=A n; let F:= V n; obtain ⟨hK,hS,hM,hU,hb⟩:= h.1 n; obtain ⟨he,ht,h,H,hP⟩:= hp.1 n
    refine ⟨fun k u=>?_,⟨fun U s d p hv hi=>?_,fun U=>?_⟩,fun x d hi v=>?_,?_,hb.add hP⟩
    · simp only [Pi.add_apply,aura_add,hK,he]
    · simp only [Pi.add_apply,aura_add,hS.port U s d p hv hi,ht.port U s d p hv hi]
    · simp only [Pi.add_apply,new_add, ← hS.lane,← ht.lane]
    · simp only [Pi.add_apply,Matrix.add_mul,Matrix.mul_add,hM x d hi v,h x d hi v]
    simp [hU,H]
  intro f F N L d ht U; simp only [Pi.add_apply,Matrix.add_mul,Matrix.mul_add,h.2 L d ht U,hp.2 L d ht U]
lemma Vital.tribute {I:Type}{C:I→Bloom k}(he: Fractal C r b)(hr:0<r)(hp : 0<k)(h:∀ n,Majestic (dust C n)): Vital (dust C):=by
  refine ⟨fun n=>?_,fun {f F m} L p hP U=> raw he _ L hP⟩
  refine ⟨prism he,h n,fun x d ht U=>?_,?_, serenity he hr⟩
  · rw [pull_one]; exact raw he U (parallel x) ht
  unfold dust; have hh i:(C i).tonic 0 (1:Grid n)=0:=(C i).tonic_one _ hp; simp only [hh,tsum_zero]


lemma league_on {U:X.Board false false} (h : X.League U): ∃ w C:ℝ,0<w∧0≤C ∧ ∀ i,glyph (traceG _) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst (fun x=>(U i x:Sheet (X.s i))) w C:=by
  obtain ⟨w,C,hw,hc,H⟩:=h
  refine ⟨_,_,hw,hc,fun i y z=>?_⟩
  let r:=X.ratio i; have hf (x y:Site (X.s i)): Push.Uniform.Decay w (r.embed x) (r.embed y) ≤ Push.Uniform.Decay w x y:=by
    unfold Push.Uniform.Decay; apply Real.exp_monotone; rw [Next.Rank.Station.both]; push_cast; have ht : (1:ℝ)≤r.count.val:=by exact_mod_cast r.count.property
    exact mul_le_mul_of_nonpos_left (le_mul_of_one_le_left (by positivity) ht) (neg_nonpos.mpr hw.le)
  have hQ := H i y z
  let k:= y.1
  let g:= Push.Uniform.Decay w (r.embed k) (r.embed z.1); let h :=Push.Uniform.Decay w k z.1
  have hp:C*g ≤ C*h:=mul_le_mul_of_nonneg_left (hf ..) hc
  have hF:= hQ.patron hp -- fails defeq
  have hx : 0 ≤ C*h:=hF.fee
  refine ⟨hw,hx,hF.host,hF.born, fun a=>(hF.walks a).trans ?_,fun i j=>(hF.wandered i j).trans ?_⟩
  · exact mul_le_mul_of_nonneg_left (hf ..) hx
  exact mul_le_mul_of_nonneg_left (mul_le_mul (hf ..) (hf ..) (Push.Uniform.decay_pos ..).le (Push.Uniform.decay_pos ..).le) hx
lemma metropolis (P:Plan j){F:X.Board false false}(V:T→ Train j)(H:X.League F) : ∃ w C:ℝ,0<w∧0 ≤ C∧ ∀ i,glyph (traceG _) Push.Uniform.bolt (Prod.fst (β:=Fiber)) Prod.fst (fun x=> (show Sheet (X.s i) from F i x)-wood P (n:=X.s i) 0 (V i) (Stationary.input su _ x)) w C := by
  obtain ⟨r,b,hC,hc,K⟩:=Rudder.pays_all P
  choose J G hQ hF using fun i=> K (V i)
  obtain ⟨w,c,hp,h,hW⟩:= attainable 0 hC (duty*b)
  obtain ⟨a,d,ht,h',Y⟩:= league_on H; have hz:= lt_min hp ht
  refine ⟨_,_,hz,add_nonneg h' (show 0≤c*(duty*b) from mul_nonneg h (mul_nonneg duty_pos.le hc.le)),fun i=>?_⟩
  have hx B:dust (queen∘G i) (X.s i) B=wood P 0 (V i) B:=by unfold dust; simp_rw [Function.comp_apply, queen_rides]; exact (hF i ..).tsum_eq
  have hm:= hW (J i) _ (Eyrie.trek (hQ i)) (X.s i); simp_rw [hx] at hm
  have h := (Y i|>.reduces hz (min_le_right ..) h' le_rfl).plus (hm.minus|>.reduces hz (min_le_left ..) (mul_nonneg h (mul_nonneg duty_pos.le hc.le)) le_rfl)
  simp_rw [sub_eq_add_neg]; exact h
end YM.QCD.Orbit.Birth
