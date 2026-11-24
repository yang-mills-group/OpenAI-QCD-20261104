import YM.MassiveBridge.Join
import YM.Work.C24 -- unlabelled spacetime reshaping
/-!
# Mixed heights give W positivity and a concrete chamber embedding.

As in YM/Work/C24, use Lebesgue products compatible with the same
Euclidean/Spacetime coordinate. No Lorentz invariance assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge
open Set Filter Function MeasureTheory WithLp
open Boundary hiding Fields Letter Sentence Surface Waves
open scoped Topology InnerProductSpace BigOperators NNReal ComplexOrder
variable {n m : ℕ} {X : Fields} {S : X.Kernel} {V : Chamber S timeAxis}
open Join
open Bid (bothH bothP)
open Work.C24 (merger toward ordered eventually_pos preserves)
def bothL (v : Fin n → Letter X) (w : Fin m → Letter X) : Fin (n + m) → Letter X :=
  Fin.append (fun i => Letter.op (v i.rev)) w

def bothTest (v : Fin n → Letter X) (w : Fin m → Letter X) :=
  Joint.materialize (n + m) fun i => (bothL v w i).2

lemma bothTest_at (v : Fin n → Letter X) (w : Fin m → Letter X) (x : Points n) (y : Points m) :
    bothTest v w (bothP x y) = (starRingEnd ℂ) (Joint.materialize n (fun i => (v i).2) x) *
      Joint.materialize m (fun i => (w i).2) y := by
  simp only [bothTest, Joint.material_at, Fin.prod_univ_add, bothL, bothP, points_apply,
    Fin.append_left, Fin.append_right, Letter.op, Probe.bar_at, map_prod]
  exact congrArg (· * _) (Equiv.prod_comp Fin.revPerm (fun i => star ((v i).2 (x i))))

lemma bothL_get (v w : Sentence X) :
    List.ofFn (bothL v.get w.get ) = Sentence.rev v ++ w := by
  unfold bothL Sentence.rev
  rw [List.ofFn_fin_append, List.ofFn_get]
  congr 1
  refine List.ext_get (by simp) (fun i h h' => ?_)
  rw [List.get_ofFn, List.get_eq_getElem (l := List.reverse _), List.getElem_reverse, List.getElem_map]
  congr 1
  rw [List.get_eq_getElem]
  congr 1
  simp [Fin.val_rev]; omega

lemma expect_ofFn (W : Surface X) (q : Fin n → Letter X) :
    W.expect (List.ofFn q) = W.W n (fun i => (q i).1) (Joint.materialize n fun i => (q i).2) := by
  have key (b : Sentence X) (k : ℕ) (h : b.length = k) (v : Fin k → Letter X)
      (he : ∀ i, b.get i = v (Fin.cast h i)) :
      W.expect b = W.W k (fun i => (v i).1) (Joint.materialize k fun i => (v i).2) := by
    subst k; simp only [Surface.expect, he, Fin.cast_refl, id_eq]
  exact key _ _ (by simp) q (List.get_ofFn _)

lemma kernel_as (W : Surface X) (v w : Sentence X) :
    W.kernel v w = W.W (v.length + w.length) (bothT (fun i => (v.get i).1) (fun i => (w.get i).1) )
      (bothTest v.get w.get ) := by
  rw [Surface.kernel, ← bothL_get, expect_ofFn]
  unfold bothTest
  congr 2
  funext i; refine Fin.addCases ?_ ?_ i <;> (intro j; simp [bothT, bothL, Letter.op])

variable {B : MatrixCap V} {A : Spread V} {F : Waves X} {W : Surface X}

lemma integrated (link : B.concretized A) (h : F.Region S) (int : F.NonTangentialFree W) (v w : Sentence X)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    inner ℂ (B.heatCup v t) (B.heatCup w u) = ∫ x, F.restricted
        (bothT (fun i => (v.get i).1) (fun i => (w.get i).1) )
        (bothH (Small.profile t v.length) (Small.profile u w.length)) x * bothTest v.get w.get x := by
  let a := Small.profile t v.length
  let b := Small.profile u w.length
  let M := bothTest v.get w.get
  let d (x : Points (v.length + w.length)) := F.restricted
    (bothT (fun i => (v.get i).1) (fun i => (w.get i).1) ) (bothH a b) x * M x
  let e := merger (n := v.length) (m := w.length)
  have ha : a ∈ positiveHeight _ := Small.imminent ht
  have hb : b ∈ positiveHeight _ := Small.imminent hu
  have hi : Integrable (d ∘ e) := (preserves.integrable_comp_emb e.toHomeomorph.measurableEmbedding).mpr
    (int.int _ _ _ (ordered ha hb) _)
  calc
    _ = ∫ x : Points v.length, ∫ y : Points w.length, (d ∘ e) (x, y) := by
      rw [MatrixCap.heatCup, ← inner_conj_symm, ← integral_inner (MatrixCap.shot_int _ _ _ _ _ (Small.suitable (n:=v.length) ht)), ← integral_conj]
      apply integral_congr_ae; filter_upwards with x
      rw [inner_conj_symm, MatrixCap.heatCup, ← integral_inner (MatrixCap.shot_int _ _ _ _ _ (Small.suitable (n:=w.length) hu))]
      apply integral_congr_ae; filter_upwards with y
      change inner ℂ (_ • B.shot _ _ _ a x) (_ • B.shot _ _ _ b y) = d (bothP x y)
      rw [inner_smul_left, inner_smul_right, pointJoined link h (Small.suitable (n:=v.length) ht).1.1 (Small.suitable (n:=w.length) hu).1.1 a b x y _ _ (ample_room (Small.suitable (n:=v.length) ht)) (ample_room (Small.suitable (n:=w.length) hu))]
      dsimp only [d, M]
      rw [bothTest_at]; ring
    _ = ∫ z, (d ∘ e) z ∂(volume.prod volume) := (integral_prod _ hi).symm
    _ = ∫ x, d x := preserves.integral_comp e.toHomeomorph.measurableEmbedding d

lemma kernel_limit {F : Waves X} {B : MatrixCap V} {A : Spread V} (link : B.concretized A)
    (h : F.Region S) (int : F.NonTangentialFree W) (v w : Sentence X) :
    Tendsto (fun p : ℝ × ℝ => inner ℂ (B.heatCup v p.1) (B.heatCup w p.2)) (till ×ˢ till) (𝓝 (W.kernel v w)) := by
  rw [kernel_as W v w]
  have H := (int.corner _ (bothT (fun i => (v.get i).1) (fun i => (w.get i).1)) (bothTest v.get w.get)).comp
    (toward v.length w.length)
  apply H.congr'
  filter_upwards [eventually_pos] with p hp using (integrated link h int v w hp.1 hp.2).symm

structure Outfield (W : Surface X) (C : Chamber S timeAxis) where
  toFun : Sentence X → C.H
  at_pair x y : inner ℂ (toFun x) (toFun y)=W.kernel x y
  vacuum : toFun []=C.omega
  volume (v b) : toFun (shiftBy b v)=C.flow.unit.translation b (toFun v)

lemma outfield (link : B.concretized A) (h : F.Region S) (hb : F.NonTangentialFree W) : Nonempty (Outfield W V) := by
  choose Y hY using fun x : Sentence X => norms_kernel V.H _ _ (kernel_limit link h hb x x)
  refine ⟨Y,?_,?_,?_⟩
  · intro x y
    exact tendsto_nhds_unique (((hY x).comp tendsto_fst).inner ((hY y).comp tendsto_snd)) (kernel_limit link h hb x y)
  · exact tendsto_nhds_unique (hY _) (tendsto_const_nhds.congr' (Eventually.of_forall fun i => (B.omega i).symm))
  intro v x
  exact tendsto_nhds_unique_of_eventuallyEq (hY _) ((V.flow.unit.translation x).continuous.continuousAt.tendsto.comp (hY _)) (Eventually.mono self_mem_nhdsWithin fun i hi => MatrixCap.heatCup_shift B v x i hi)
namespace Outfield
variable {W : Surface X} (Z : Outfield (S:=S) W V)
include Z
lemma safe : Analysis.NNKernel W.kernel := by
  have he := Boundary.Fields.hilbertNonnegative V.H Z.toFun
  rw [show W.kernel = _ from funext fun x => funext fun y => (Z.at_pair x y).symm]; exact he
lemma soak (p : Fields.Euclidean S) : W.expect []=1 := by
  have he : inner ℂ V.omega V.omega=W.expect [] := by rw [← Z.vacuum,Z.at_pair];rfl
  rw [← he,inner_self_eq_norm_sq_to_K,show ‖V.omega‖=1 from nil_norm V.GNS p]; simp
end Outfield
end YM.Massive.Bridge
