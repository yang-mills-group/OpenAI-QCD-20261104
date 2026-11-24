import YM.MassiveBridge.Soil
import YM.Work.C28

/-!
# Covariant spacetime action on the whole Hilbert space

On one double cover; not assume Group instance in target.
Lifting to double cover of Poincare change translations kernel by coord p
(not spin). Proofs largely adapted from Fields/Motion and Work/C28.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge
open Function Set Filter Complex Analysis Kernel Mink MeasureTheory Distribution
open Boundary hiding Fields Surface Waves Letter Sentence Soil Scroll Action
open Poincare
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {S:Fields} {W:Surface S} {Q:Sequence}{P:Calibration Q}{T:S.Kernel}{Y:Waves S} {n:ℕ}

abbrev Travel := RealSpin × E4 -- no instance for Group
namespace Travel
def asMink (p:Travel): Poincare:=⟨p.1.coord,p.2⟩
def stand : Travel:=(1,0)
def spin (p:RealSpin): Travel:=(p,0)
def across (p:E4): Travel:=(1,p)
def follow (p q:Travel): Travel:=(p.1*q.1,sends p.asMink q.2)
lemma asFollow(p q:Travel) : (follow p q).asMink=p.asMink*q.asMink:=rfl
lemma asCont : Continuous asMink:= standard.continuous_iff.mpr (continuous_prodMk.mpr ⟨show Continuous (fun p:Travel=> p.1.coord) from continuous_fst.comp (continuous_subtype_val.comp continuous_fst),continuous_snd⟩)
lemma acre (p:E4) (q:RealSpin): follow (across p) (spin q)=(q,p):= by
   apply Prod.ext
   · exact one_mul _
   change (translation p).sends 0 = _; rw [as_move]; simp
lemma beside (p:RealSpin)(a:E4): follow (spin p) (across a) =(p,p.coord.act a):=by
   apply Prod.ext
   · exact mul_one _
   exact as_active ..
lemma over (p q:E4): follow (across p) (across q)=across (p+q):= by
   apply Prod.ext
   · exact one_mul _
   change (translation p).sends q = _;rw [as_move]; exact add_comm ..
lemma inert (p q:RealSpin): follow (spin p) (spin q)=spin (p*q):=by exact Prod.ext (show (follow (spin p) (spin q)).1=p*q from rfl) (base _)
end Travel

namespace WSpins
variable (K:WSpins S)
def read (p:Travel)(i:Letter S): Letter S:= (K.spin p.1 i.1, Joint.push p.asMink i.2)
lemma stays (i:Letter S): K.read Travel.stand i=i:=by
  apply Prod.ext
  · simp [read,Travel.stand]
  change Joint.push 1 i.2 = _; ext1; rw [Joint.push_at,inv_one,Poincare.sends_one]
lemma travels (p q:Travel)(s:Letter S): K.read (Travel.follow p q) s=K.read p (K.read q s):=by
  apply Prod.ext
  · simp [read,Travel.follow]
  change Joint.push _ s.2 = Joint.push p.asMink _; ext1; rw [Joint.push_at,Joint.push_at]
  change s.2 _ = Joint.push q.asMink s.2 _
  rw [Joint.push_at,Travel.asFollow,mul_inv_rev,Poincare.sends_mul]
lemma star_read(p:Travel)(i:Letter S) : Letter.op (K.read p i)= K.read p (Letter.op i):=by
  apply Prod.ext
  · exact (K.conjugate _ _).symm
  ext1 x
  change Probe.bar _ x=Joint.push _ _ x
  simp [read, Joint.push_at, Letter.op]

def walk (p:Travel)(w:Sentence S): Sentence S:= w.map (K.read p)
lemma standing (w:Sentence S): K.walk Travel.stand w=w:=by
  unfold walk; rw [show K.read Travel.stand=id from funext (K.stays),List.map_id]
lemma following (p q:Travel)(w:Sentence S):K.walk (Travel.follow p q) w=K.walk p (K.walk q w):=by
  unfold walk; rw [List.map_map]; exact congr_arg (fun f=> w.map f) (funext (K.travels p q))
lemma rev_walk (p:Travel) (w:Sentence S): Sentence.rev (K.walk p w)= K.walk p (Sentence.rev w):=by
   unfold walk Sentence.rev; rw [List.map_map,List.map_reverse,List.map_map,funext (show ∀ a:Letter S, (Letter.op ∘ K.read p) a=(K.read p ∘ Letter.op) a from fun a=>K.star_read p a)]
end WSpins

namespace Surface
open WSpins
variable (K:WSpins S) (W:Surface S)
def Transforms := ∀ i j:Sentence S,∀ p:Travel,W.kernel (K.walk p i) (K.walk p j)=W.kernel i j
def Strong := ∀ i j:Sentence S, Continuous fun p=> W.kernel i (K.walk p j)
/-- A moving finite set of pinned labels, tested on a simultaneously moving joint test. -/
lemma continuous_pinned {X : Type*} [TopologicalSpace X] (d : ℕ) [FiniteDimensional ℂ (S.level d)]
    (v : X → Fin n → ↥(S.level d)) (f : X → Joint n) (hv : ∀ i, Continuous (fun x => v x i)) (hf : Continuous f) :
    Continuous (fun x => W.W n (fun i => (S.level d).subtype (v x i)) (f x)) := by
  let B := Module.finBasis ℂ (↥(S.level d))
  let T : MultilinearMap ℂ (fun _ : Fin n => ↥(S.level d)) (Distn (Points n)) :=
    (W.W n).compLinearMap (fun _ => (S.level d).subtype)
  change Continuous (fun x => T (v x) (f x))
  let b (k : Fin n → Fin (Module.finrank ℂ (↥(S.level d)))) (i : Fin n) := B (k i)
  let c (k : Fin n → Fin (Module.finrank ℂ (↥(S.level d)))) (x : X) := ∏ i, B.repr (v x i) (k i)
  -- expand over *all* basis tuples (even if a coefficient crosses zero)
  have he (x : X) : T (v x) = ∑ k, c k x • T (b k) := by
    have hx : v x = fun i => ∑ j, B.repr (v x i) j • B j :=
      funext fun i => (B.sum_repr _).symm
    conv_lhs => rw [hx]
    rw [MultilinearMap.map_sum]
    exact Finset.sum_congr rfl fun k _ => T.map_smul_univ (fun i => B.repr (v x i) (k i)) (b k)
  simp_rw [he, sum_apply, smul_apply]
  refine continuous_finsetSum _ fun k _ => (show Continuous (c k) from ?_).smul ((T (b k)).continuous.comp hf)
  exact continuous_finsetProd _ (fun i _ => ((B.coord (k i)).continuous_of_finiteDimensional.comp (hv i)))

lemma reads {U:Type*}[TopologicalSpace U](E:S.System P)(w:Fin n→Letter S) (g:Fin n→U→Travel)(hg:∀ i,Continuous (g i)): Continuous fun x => W.expect (List.ofFn (fun i=> K.read (g i x) (w i))):=by
  obtain ⟨d,z,hz⟩:=Rotate.cover_cap E (fun i=> (w i).1)
  haveI := E.finite d
  have hu i : (w i).1=(S.level d).subtype (z i):=congr_fun hz i
  let l (t:U) i : S.level d:=⟨K.spin (g i t).1 (z i).val,K.lives d _ _ (z i).property⟩
  have h (i): Continuous (fun x=> l x i):= continuous_induced_rng.mpr ((K.continuous_spin (z i).val).comp (continuous_fst.comp (hg i))) --
  simp_rw [expect_ofFn, WSpins.read, hu]
  apply continuous_pinned W d l _ h
  exact (Joint.jointCont n).comp (show Continuous (fun t=> (fun i=> Joint.push (g i t).asMink (w i).2)) from continuous_pi (fun i=> (Work.C28.continuous_push Work.C08.answer _).comp (Travel.asCont.comp (hg i))))

lemma walk_ofFn_get (p:Travel) (w:Sentence S) : K.walk p w=List.ofFn (K.read p ∘ w.get):=by rw [←List.map_ofFn,List.ofFn_get];rfl
lemma strong (E:S.System P): W.Strong K:=by
  intro i j
  let l := Sentence.rev i
  let w := Fin.append l.get j.get
  let g : Fin (l.length+j.length) → Travel → Travel := Fin.append (fun _ : Fin l.length => fun _=> Travel.stand)
    (fun _ : Fin j.length => id)
  have hg (a) : Continuous (g a) := by
    refine Fin.addCases ?_ ?_ a
    · intro a; simp only [g, Fin.append_left]; exact continuous_const
    intro a; simp only [g, Fin.append_right]; exact continuous_id
  have hwords (p) : l ++ K.walk p j = List.ofFn (fun a => K.read (g a p) (w a)) := by
    rw [show (fun a => K.read (g a p) (w a)) = Fin.append l.get (K.read p ∘ j.get) from ?_,
      List.ofFn_fin_append, List.ofFn_get, walk_ofFn_get]
    funext a; refine Fin.addCases ?_ ?_ a
    · intro a
      simp only [g, w, Fin.append_left]
      exact K.stays _
    intro a; simp only [g, w, Fin.append_right]; rfl
  change Continuous fun p => W.expect (l ++ K.walk p j)
  simp_rw [hwords]
  exact reads K W E w g hg


variable {W}
lemma invariant_w (E:S.System P)(H:Fields.Euclidean T)(e:Y.Region T)(h:Y.NonTangentialFree W)(hp:Y.Breathes)(p:Travel)(w:Sentence S): W.expect (K.walk p w)= W.expect w:=by
  rw [walk_ofFn_get,expect_ofFn]
  let f := fun i=> (w.get i).2
  let v := fun i=> (w.get i).1
  change W.W _ (K.spin p.1 ∘ v) (Joint.materialize _ (fun i=> Joint.push _ (f i))) = W.W _ v (Joint.materialize _ f)
  rw [← Joint.tests,Work.C28.gpush_split,Rotate.translations H e h]
  change W.W _ _ (Probe.along (togetherL p.1.coord _).symm _) = _
  rw [← Work.C09.motion_push]
  exact Rotate.every_motion E H K e h hp _ v _
lemma transforms (E:S.System P)(H:Fields.Euclidean T)(e:Y.Region T)(h:Y.NonTangentialFree W)(hp:Y.Breathes): W.Transforms K:=by
    intro i j p
    unfold kernel; rw [rev_walk]; rw [show K.walk p (Sentence.rev i) ++ K.walk p j=K.walk p _ from (List.map_append ..).symm] --
    exact W.invariant_w K E H e h hp _ _
end Surface

structure Action (D:Hilbert) where
  V: Travel → D.Op
  one : V Travel.stand= ContinuousLinearMap.id ℂ _
  follow (p q:Travel): V (Travel.follow p q)=(V p).comp (V q)
  usual (p:Travel)(x:D): ‖V p x‖=‖x‖
  strong (x:D): Continuous (fun p=> V p x)

namespace Soil
variable (Z:Soil W)
lemma universal_embed {M : Hilbert} (q : Sentence S → M) (h : ∀ x y, inner ℂ (q x) (q y)=W.kernel x y) :
    ∃ U : Z.H→L[ℂ] M, ‖U‖≤1 ∧ (∀ i,U (Z.plant i)=q i) ∧ ∀ v : Z.H,
    ‖U v‖=‖v‖ := by
  let F := Finsupp.linearCombination ℂ q
  have he (x y : Scroll S) : inner ℂ (F x) (F y)=inner ℂ (Z.stems x) (Z.stems y) := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add p v hP hQ => simp only [map_add,inner_add_left,hP,hQ]
    | single i a =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add p v hP hQ => simp only [map_add,inner_add_right,hP,hQ]
      | single j b => simp only [F,Gram.stems,Finsupp.linearCombination_single, inner_smul_left,inner_smul_right,Z.measure,h]
  have hp x : ‖F x‖=‖Z.stems x‖ := by
    nth_rw 1 [@norm_eq_sqrt_re_inner ℂ]; rw [he, ← @norm_eq_sqrt_re_inner ℂ]
  obtain ⟨U,hU,H⟩ := Z.by_bound q 1 zero_le_one (fun u => by rw [one_mul]; exact (hp u).le)
  have ht u : U (Z.stems u)=F u := by
    induction u using Finsupp.induction_linear with
    | zero => simp
    | add i j hi hj => simp only [map_add,hi,hj]
    | single i a => simp [F,Gram.stems,H]
  exact ⟨U,hU,H,fun i => congr_fun
    (Z.whole.equalizer U.continuous.norm continuous_norm (funext fun j => (congr_arg _ <| ht j).trans (hp j))) i⟩

lemma strong_life (Y : Travel → Z.H.Op) (h : ∀ p,∀ v : Z.H, ‖Y p v‖=‖v‖) (hp : ∀ i,Continuous fun p => Y p (Z.plant i)) :
    ∀ v : Z.H,Continuous fun p => Y p v := by
  have he (i : Scroll S) : Continuous fun p => Y p (Z.stems i) := by
    induction i using Finsupp.induction_linear with
    | zero => simp; exact continuous_const
    | add i j hi hj => simp_rw [map_add]; exact hi.add hj
    | single i b => simp_rw [Kernel.Gram.stems,Finsupp.linearCombination_single,map_smul]; exact continuous_const.smul (hp i)
  intro v; apply continuous_iff_continuousAt.mpr; intro p
  apply Metric.tendsto_nhds.mpr; intro ε hε
  obtain ⟨_,⟨i,rfl⟩,hi⟩ := Metric.mem_closure_iff.mp (Z.whole v) (ε/3) (by positivity)
  filter_upwards [Metric.tendsto_nhds.mp (he i|>.tendsto p) (ε/3) (by positivity)] with u hu
  have hU k : dist (Y k v) (Y k (Z.stems i))=dist v (Z.stems i) := by rw [dist_eq_norm,dist_eq_norm, ← map_sub,h]
  apply lt_of_le_of_lt (dist_triangle _ (Y u (Z.stems i)) _)
  have ht := dist_triangle (Y u (Z.stems i)) (Y p (Z.stems i)) (Y p v)
  rw [dist_comm (Y p (Z.stems i)) (Y p v),hU] at ht
  rw [hU]; linarith

lemma mobilize (X : WSpins S) (hp : W.Transforms X) (hh : W.Strong X) :
    ∃ Y : Action Z.H,∀ i p,Y.V p (Z.plant i)=Z.plant (X.walk p i) := by
  choose U hU HT HS using fun p => Z.universal_embed (M:=Z.H) (Z.plant ∘ X.walk p)
    (fun i j => (Z.measure (X.walk p i) (X.walk p j)).trans (hp i j p))
  have he p i : U p (Z.plant i)=Z.plant (X.walk p i) := HT p i
  let B : Action Z.H :=
    { V := U
      one := Z.by_bud fun i => by rw [he,X.standing]; rfl
      follow := fun p q => Z.by_bud fun i => by rw [ContinuousLinearMap.comp_apply,he,he,he,X.following]
      usual := HS
      strong := strong_life Z U HS fun i => by
        simp_rw [he]
        apply continuous_iff_continuousAt.mpr; intro p; apply OS.ketC
        · simp_rw [Z.measure]; unfold Surface.Transforms at hp; simp_rw [hp]; exact continuousAt_const
        simp_rw [Z.measure]; exact (hh _ i).continuousAt }
  exact ⟨B,fun i p => HT p i⟩

lemma domain (K:WSpins S)(U:Action Z.H)(h:∀ i p,U.V p (Z.plant i)=Z.plant (K.walk p i))(p:Travel)(x:Z.land):U.V p x.val∈Z.land:=by
  obtain ⟨i,hv⟩:=x.property
  rw [← hv]; clear hv
  induction i using Finsupp.induction_linear with
    | zero => rw [map_zero,map_zero]; exact Z.land.zero_mem
    | add i j hi hj => rw [map_add,map_add]; exact Z.land.add_mem hi hj
    | single i z => simp_rw [Gram.stems,Finsupp.linearCombination_single,map_smul,h]; exact Z.land.smul_mem _ (Z.seed _).property
lemma covariance (K:WSpins S)(U:Action Z.H)(h:∀ i p,U.V p (Z.plant i)=Z.plant (K.walk p i))(p:Travel)(x:S.W)(f:Test4)(a:Z.land):
    U.V p (Z.starter W.symbol x f a).val=
      (Z.starter W.symbol (K.spin p.1 x) (Joint.push p.asMink f) (⟨U.V p a.val,Z.domain K U h p a⟩:Z.land)).val:= by
  let hV (p : Travel): MapsTo (U.V p) (Z.land : Set Z.H) Z.land := fun x hx=> Z.domain K U h p ⟨x,hx⟩
  let g : Z.land→ₗ[ℂ] Z.land := (U.V p).toLinearMap.restrict (p:=Z.land) (q:=Z.land) (hV p)
  have ht i : g (Z.seed i)=Z.seed (K.walk p i) := Subtype.ext (h i p)
  have hp : g.comp (Z.beginsOp (x,f))=(Z.beginsOp (K.spin p.1 x,Joint.push p.asMink f)).comp g := by
    apply Z.buds; intro i
    rw [LinearMap.comp_apply,LinearMap.comp_apply,Z.actual, ht,ht, Z.actual]; rfl
  exact congr_arg Subtype.val (LinearMap.congr_fun hp a)
end Soil
end YM.Massive.Bridge
