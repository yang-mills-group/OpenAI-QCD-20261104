import YM.MassiveBridge.ScalarSlot
import YM.Work.C25
import YM.Work.C29

/-!
# W left domain via GNS: Z, grading, W-bulk, faithful,
# slot-temperance, derivatives and smeared identity

 Companion to graded spacetime action. Proofs adapted from
 YM/{Fields/Stems,Work/{C25,C26,C29}}. No W hypotheses in Goal, starts
 after previous bridge.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge
open Function Set Filter Complex Analysis Kernel Mink MeasureTheory Distribution
open Boundary hiding Fields Surface Waves Letter Sentence Soil Scroll
open Probe
open Work.C29 (materialLinear)
open scoped Topology BigOperators InnerProductSpace ComplexOrder ComplexConjugate
variable {S:Fields} {n : ℕ}
abbrev Soil (W : Surface S) := Kernel.Gram (W.kernel)
abbrev Scroll (S : Fields) := Sentence S →₀ ℂ

namespace Surface
/-- these ports will come from W's actual tested values + limits, differ
from S point permutation. -/
def Symbol (W : Surface S) := ∀ a b : Sentence S,
    ∃ U : S.W →ₗ[ℂ] Test4 →ₗ[ℂ] ℂ, ∀ (x : S.W) (f : Test4), W.expect (a++((x,f)::b)) = U x f

def Cam (W : Surface S) := ∀ a b : Sentence S, ∀ x y : S.W,
    Continuous fun p : Test4 × Test4 => W.kernel ((x,p.1)::a) ((y,p.2)::b)

def Marker (W : Surface S) (x : S.W) := ∀ a b : Sentence S, ∀ f : Test4, W.expect (a++((x,f)::b))=0

def Persists (W : Surface S) := ∀ x, W.Marker x → x=0
variable (W : Surface S)

lemma expectCast (v : Fin n → Letter S) {b : Sentence S} (h : n = b.length)
    (e : ∀ i, b.get (Fin.cast h i) = v i) :
    W.expect b = W.W n (Prod.fst ∘ v) (Joint.materialize n (Prod.snd ∘ v)) := by
  subst n
  have : b.get = v := funext e
  simp only [Surface.expect, this, Function.comp_def]

lemma expectOfFn (v : Fin n → Letter S) :
    W.expect (List.ofFn v) = W.W n (Prod.fst ∘ v) (Joint.materialize n (Prod.snd ∘ v)) :=
  expectCast W v (by simp) (by simp)

/-- At one slot of a fixed-arity word insert both a label and a test. -/
lemma mixedSlot (v : Fin n → Letter S) (i : Fin n) :
    ∃ U : S.W →ₗ[ℂ] Test4 →ₗ[ℂ] ℂ, ∀ x f,
      W.expect (List.ofFn (update v i (x,f))) = U x f := by
  let A := (W.W n).toLinearMap (Prod.fst ∘ v) i
  let B := (materialLinear n).toLinearMap (Prod.snd ∘ v) i
  let U : S.W →ₗ[ℂ] Test4 →ₗ[ℂ] ℂ :=
    { toFun := fun x => (A x).toLinearMap.comp B
      map_add' := by intro x y; ext f; exact DFunLike.congr_fun (A.map_add x y) _
      map_smul' := by intro c x; ext f; exact DFunLike.congr_fun (A.map_smul c x) _ }
  refine ⟨U,fun x f => ?_⟩
  rw [expectOfFn, Function.comp_update, Function.comp_update]; rfl

lemma insertSlot {m n : ℕ} {α : Type*} (v : Fin m → α) (w : Fin n → α) (x y : α) :
    update (Fin.append v (Fin.cons x w)) (Fin.natAdd m 0) y = Fin.append v (Fin.cons y w) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · have h : Fin.castAdd (n+1) i ≠ Fin.natAdd m 0 := by
      apply Fin.ne_of_lt
      exact (show i.val < m + 0 by simp)
    simp [h]
  induction j using Fin.cases with
  | zero => simp
  | succ j => simp [Fin.natAdd_inj]

lemma symbol : W.Symbol := by
  intro a b
  obtain ⟨U,hU⟩ := mixedSlot W (Fin.append a.get (Fin.cons (0,0) b.get)) (Fin.natAdd a.length 0)
  exact ⟨U,fun x f => by simpa only [insertSlot, List.ofFn_fin_append, List.ofFn_cons, List.ofFn_get] using hU x f⟩

/-- Continuous smearings slot by slot, with all label components constant. -/
lemma continuousExpect {T : Type*} [TopologicalSpace T] (v : T → Fin n → Letter S)
    (x : Fin n → S.W) (he : ∀ p i, (v p i).1 = x i) (hc : ∀ i, Continuous fun p => (v p i).2) :
    Continuous (fun p => W.expect (List.ofFn (v p))) := by
  have h := (W.W n x).continuous.comp ((Joint.jointCont n).comp (continuous_pi hc))
  refine h.congr fun p => ?_
  rw [expectOfFn, show Prod.fst ∘ v p = x from funext (he p)]
  rfl

lemma cam : W.Cam := by
  intro a b x y
  let r := Sentence.rev a
  let v (p : Test4 × Test4) : Fin (r.length + ((b.length+1)+1)) → Letter S :=
    Fin.append r.get (Fin.cons ((S.adj timeAxis x), Probe.bar p.1) (Fin.cons (y,p.2) b.get))
  have he (p : Test4 × Test4) : W.kernel ((x,p.1)::a) ((y,p.2)::b) = W.expect (List.ofFn (v p)) := by
    simp only [v, List.ofFn_fin_append, List.ofFn_cons, List.ofFn_get]
    simp [Surface.kernel, Sentence.rev, r, Letter.op]
  simp_rw [he]
  apply continuousExpect W v (Prod.fst ∘ v (0,0))
  · intro p i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp [v]
    induction j using Fin.cases with
    | zero => simp [v]
    | succ j => induction j using Fin.cases <;> simp [v]
  intro i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simpa [v] using (continuous_const (X := Test4 × Test4) (y := (r.get i).2))
  induction j using Fin.cases with
  | zero => simpa [v, Function.comp_def] using (Probe.bar (V := E4)).continuous.comp (continuous_fst (Y := Test4))
  | succ j =>
    induction j using Fin.cases with
    | zero => simpa [v] using (continuous_snd (X := Test4) (Y := Test4))
    | succ i => simpa [v] using (continuous_const (X := Test4 × Test4) (y := (b.get i).2))

/-- Test in the slot even after reordering (where it need no longer be the head). -/
lemma marker_on_joint (density : Bid.C25) (U : Surface S) (v : Fin n → S.W)
    (i : Fin n) (hi : U.Marker (v i)) : U.W n v = 0 := by
  have h1 (f : Fin n → Test4) : U.W n v (Joint.materialize n f) = 0 := by
    let q : Fin n → Letter S := fun i => (v i, f i)
    obtain ⟨a,b,h⟩ := List.append_of_mem (List.mem_ofFn.mpr ⟨i,rfl⟩ : q i ∈ List.ofFn q)
    have e := expectCast U q (b:=List.ofFn q) (by simp) (by simp)
    change U.expect (List.ofFn q) = U.W n v (Joint.materialize n f) at e
    rw [← e,h]; exact hi a b (f i)
  have e : Submodule.span ℂ (range (Joint.materialize n)) ≤ LinearMap.ker (U.W n v).toLinearMap := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f,rfl⟩
    exact h1 f
  have H := Submodule.topologicalClosure_minimal _ e (U.W n v).isClosed_ker
  rw [density n] at H
  ext1 f
  exact H (Submodule.mem_top)

end Surface

namespace Soil
variable {W : Surface S} (Z : Soil W)
abbrev land : Submodule ℂ Z.H := LinearMap.range Z.stems
abbrev WordOp := Z.land→ₗ[ℂ] Z.land

def variety : Scroll S→ₗ[ℂ] Z.land := Z.stems.rangeRestrict

def seed (v : Sentence S) : Z.land := ⟨Z.plant v,⟨_,Z.one v⟩⟩

@[simp] lemma one_pack (v) : Z.variety (Finsupp.single v 1)=Z.seed v := Subtype.ext (Z.one _)
lemma rich : Surjective Z.variety := LinearMap.surjective_rangeRestrict _

/-- lift left concatenation with honest pair proof. -/
def machine (x : Letter S) : Scroll S →ₗ[ℂ] Z.land := Finsupp.linearCombination ℂ fun i => Z.seed (x::i)
@[simp] lemma shoot (x : Letter S) (i) (a : ℂ) : Z.machine x (Finsupp.single i a) = a • Z.seed (x::i) := by simp [machine]
lemma folds (x : Letter S) (i k) : W.kernel (x::i) k = W.kernel i ((Letter.op x)::k) := by simp [Surface.kernel,Sentence.rev]

lemma they (x : Letter S) (p q : Scroll S) : inner ℂ (Z.machine x p) (Z.variety q) = inner ℂ (Z.variety p) (Z.machine (Letter.op x) q) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hP hQ => simp only [map_add,inner_add_left,hP,hQ]
  | single i a =>
    induction q using Finsupp.induction_linear with
    | zero => simp
    | add p q hP hQ => simp only [map_add,inner_add_right,hP,hQ]
    | single j b =>
      have he (p : Letter S) k c : (Z.machine p (Finsupp.single k c)).val = c • Z.plant (p::k) := by
        rw [shoot];rfl
      change inner ℂ (Z.machine _ _).val (Z.stems _) = inner ℂ (Z.stems _) (Z.machine _ _).val
      rw [he,he]; simp [Kernel.Gram.stems,inner_smul_left,inner_smul_right,Z.measure,folds]

lemma compactor (x : Letter S) : LinearMap.ker Z.variety ≤ LinearMap.ker (Z.machine x) := by
  intro u H; apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  obtain ⟨v,hv⟩ := Z.rich (Z.machine x u)
  change Z.variety u=0 at H
  nth_rw 2 [← hv]
  rw [Z.they,H]; simp

def beginsOp (x : Letter S) : Z.WordOp := ((LinearMap.ker Z.variety).liftQ (Z.machine x) (Z.compactor x)).comp
    (LinearMap.quotKerEquivOfSurjective Z.variety Z.rich).symm.toLinearMap

@[simp] lemma press (x : Letter S) (i : Scroll S) : Z.beginsOp x (Z.variety i)=Z.machine x i := by
  unfold beginsOp; rw [LinearMap.comp_apply]
  rw [show (LinearMap.quotKerEquivOfSurjective _ Z.rich).symm.toLinearMap (Z.variety i)=
      Submodule.Quotient.mk (p:=LinearMap.ker Z.variety) i from ?_]; rfl
  exact Z.variety.quotKerEquivOfSurjective_symm_apply Z.rich i
@[simp] lemma actual (x i) : Z.beginsOp x (Z.seed i)=Z.seed (x::i) := by
  rw [← one_pack,press,shoot,one_smul]

lemma flipped (x : Letter S) (u v : Z.land) : inner ℂ (Z.beginsOp x u) v= inner ℂ u (Z.beginsOp (Letter.op x) v) := by
  obtain ⟨i,rfl⟩ := Z.rich u; obtain ⟨j,rfl⟩ := Z.rich v; rw [press,press, Z.they]
lemma splits (x y : Z.land) (h : ∀ i : Sentence S, inner ℂ (Z.seed i) x = inner ℂ (Z.seed i) y) : x=y := by
  apply ext_inner_left ℂ
  intro f
  obtain ⟨g,rfl⟩ := Z.rich f
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add p q hP hQ => simp only [map_add, inner_add_left, hP, hQ]
  | single i c =>
    rw [show Finsupp.single i c=c • Finsupp.single i (1:ℂ) from (by simp)]; rw [map_smul, inner_smul_left,inner_smul_left,one_pack,h]

lemma buds (f g : Z.WordOp) (h : ∀ i : Sentence S,f (Z.seed i)=g (Z.seed i)) : f=g := by
  ext1 i; obtain ⟨x,rfl⟩ := Z.rich i
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add p q hP hQ => simp only [map_add,hP,hQ]
  | single i c => rw [show Finsupp.single i c=c • Finsupp.single i (1:ℂ) from (by simp)];simp only [map_smul,one_pack,h]
lemma bearings (i j) : inner ℂ (Z.seed i) (Z.seed j)=W.expect (Sentence.rev i ++ j) := Z.measure i j
lemma adds_test (h : W.Symbol) (x : S.W) (f g : Test4) : Z.beginsOp (x,f+g) = Z.beginsOp (x,f)+Z.beginsOp (x,g) := by
  apply Z.buds; intro i; apply Z.splits; intro j
  obtain ⟨U,hU⟩ := h (Sentence.rev j) i
  simp only [LinearMap.add_apply,Z.actual,inner_add_right,Z.bearings,hU,map_add]
lemma scale_test (h : W.Symbol) (x : S.W) (f : Test4) (a : ℂ) : Z.beginsOp (x,a•f) = a • Z.beginsOp (x,f) := by
  apply Z.buds; intro i; apply Z.splits; intro j
  obtain ⟨U,hU⟩ := h (Sentence.rev j) i
  simp only [LinearMap.smul_apply,Z.actual,inner_smul_right,Z.bearings,hU,map_smul,smul_eq_mul]

def beginTest (h : W.Symbol) (x : S.W) : Test4→ₗ[ℂ] Z.WordOp := ⟨⟨Z.beginsOp ∘ fun f => (x,f),Z.adds_test h x⟩,fun a f => Z.scale_test h x f a⟩

def starter (h : W.Symbol) : S.W→ₗ[ℂ] Test4→ₗ[ℂ] Z.WordOp := {
    toFun := Z.beginTest h
    map_add' := by
      intro x y; ext1 f; apply Z.buds; intro i
      apply Z.splits; intro j
      obtain ⟨U,hU⟩ := h (Sentence.rev j) i
      change inner ℂ _ (Z.beginsOp _ _) = inner ℂ _ (Z.beginsOp (x,f) _ + Z.beginsOp (y,f) _)
      simp only [Z.actual, inner_add_right,Z.bearings,hU,map_add,LinearMap.add_apply]
    map_smul' := by
      intro a x; ext1 f; apply Z.buds; intro i
      apply Z.splits; intro j
      obtain ⟨U,hU⟩ := h (Sentence.rev j) i
      change inner ℂ _ (Z.beginsOp _ _) = inner ℂ _ (a • Z.beginsOp (x,f) _)
      simp only [Z.actual, inner_smul_right,Z.bearings,hU,map_smul,LinearMap.smul_apply,smul_eq_mul] }

@[simp] lemma sp (h : W.Symbol)(x : S.W)(f:Test4) : Z.starter h x f=Z.beginsOp (x,f):=rfl
lemma varies (x : S.W) (i) (h : W.Cam) : Continuous (fun f : Test4 => Z.plant ((x,f)::i)) := by
  apply continuous_iff_continuousAt.mpr; intro f
  apply OS.ketC
  · simp_rw [Z.measure]; exact ((h i i x x).comp (continuous_id.prodMk continuous_id)).continuousAt
  simp_rw [Z.measure]; exact ((h i i x x).comp (continuous_const.prodMk continuous_id)).continuousAt

lemma omega_norm (h: W.expect []=1): ‖Z.plant []‖=1:= by
    have he : inner ℂ (Z.plant []) (Z.plant []) =1 := (Z.measure [] []).trans h
    rw [@norm_eq_sqrt_re_inner ℂ,he]; simp
lemma usable (p:W.Cam) (x:S.W)(v:Z.land): Continuous fun f=> (Z.starter W.symbol x f v).val:=by
  obtain ⟨g,hg⟩ := Z.rich v
  subst v; change Continuous (fun f => (Z.beginsOp (x,f) (Z.variety g)).val)
  induction g using Finsupp.induction_linear with
  | zero => simp;exact continuous_const
  | add a b H W =>
    simp_rw [map_add]
    exact H.add W
  | single i c =>
    rw [show Finsupp.single i c=c • Finsupp.single i (1:ℂ) from (by simp)]
    simp_rw [map_smul,one_pack,actual]
    change Continuous (fun f : Test4 => c • Z.plant ((x,f)::i)); exact continuous_const.smul (Z.varies x i p)


variable {T:S.Kernel}{Q:Sequence}{P:Calibration Q}{Y:Waves S}{A:∀ n, Blanket n}{G:W.Aurora A} {v:Y.Region T} {C:Chamber T timeAxis}
lemma faithful (h:S.System P) (p:Fields.Euclidean T) (e:Y.Region T) (he:G.FullBody Y): Injective (Z.starter W.symbol):=by
  refine (injective_iff_map_eq_zero _).mpr (fun x hx=>?_) -- #
  have h1 : W.Marker x:=by
    intro a b f
    have hi : Z.beginsOp (x,f)=0 := by rw [←sp Z W.symbol,hx];rfl
    have hm := Z.bearings (Sentence.rev a) ((x,f)::b)
    rw [Sentence.rev_rev (h.reflected _)] at hm; rw [← hm, ← actual Z, hi, LinearMap.zero_apply, inner_zero_right]
  let a: Fin 2→S.W:= ![S.adj timeAxis x,x]
  have hU: W.W 2 a=0:=Surface.marker_on_joint Work.C25.answer W a 1 (by simpa [a] using h1)
  by_contra H
  obtain ⟨r,hr,hh⟩:=p.faithful x H
  let q:=points (![0,r • basis timeAxis])
  let y : Heights 2:= ![0,r]
  have hy:y∈east 2:=by intro i j hij; fin_cases i<;>fin_cases j<;> simp_all [east,y]
  have hl:=Surface.Aurora.lower G he a y 0 hy hU
  have hx0 : Boundary.trace (0: Points 2)=0:=by ext1 i; apply PiLp.ext;intro j;simp [Boundary.trace,spatial]
  have ht0 : shift (0:Points 2) y=(fun i=> (y i:ℂ)*I) := by funext i; simp [shift,time]
  have hp0 : place (0:SpacePoints 2) y=q:=by
    ext1 i; apply Mink.ext_by
    · fin_cases i <;> apply PiLp.ext<;>intro c <;> simp [place,q,spatial,position]
    fin_cases i<;>simp [place,y,q,time, basis,position]
  rw [Waves.restricted,hx0,ht0, e.roots 2 a 0 y hy,hp0] at hl
  exact (lt_irrefl (0:ℂ)) (lt_of_lt_of_le hh hl.le)

lemma local_op (h:S.System P)(p:Fields.Euclidean T)(K:WSpins S)(he:Y.Region T)(hw:Y.NonTangentialFree W)(hb:Y.Breathes)(x y:S.W)(u v:Bool)(hu:S.homogeneous u x)(hv:S.homogeneous v y)(f g: Test4)(H:Boundary.Fields.causal f g):
    (Z.beginsOp (x,f)).comp (Z.beginsOp (y,g))=(if u&&v then (-1:ℂ) else 1) • (Z.beginsOp (y,g)).comp (Z.beginsOp (x,f)):=by
   apply Z.buds; intro i; apply Z.splits; intro j
   simp only [LinearMap.smul_apply,LinearMap.comp_apply, actual, inner_smul_right,Z.bearings]; exact Contact.graded h p K he hw hb _ _ x y u v hu hv f g H
open Surface in
lemma diff_expect (p:Fields.Euclidean T)(he:Y.Region T)(hw:Y.NonTangentialFree W)(ht:G.FullBody Y)(l r:Sentence S)(x:S.W)(f:Test4)(i:Axis):
   W.expect (l ++ (S.partialD i x,f)::r)=-(if i=timeAxis then I else 1) * W.expect (l ++ (x, Reconstruction.direction i f)::r):=by
  let m := Fin.append l.get (Fin.cons (x,f) r.get)
  let j := Fin.natAdd l.length (0 : Fin (r.length+1))
  have e(y:Letter S): List.ofFn (update m j y)= l ++ y::r:=by
      simp only [m,j,insertSlot,List.ofFn_fin_append,List.ofFn_cons,List.ofFn_get]
  let y: Fin (l.length+(r.length+1))→S.W:= Prod.fst ∘ m
  let g: Fin (l.length+(r.length+1))→Test4:= Prod.snd ∘ m
  have hu : y j=x:=by simp [y,m,j]
  have hf : g j=f:=by simp [g,m,j]
  rw [←e,←e,W.expectOfFn,W.expectOfFn]
  simp only [Function.comp_update]; change W.W _ (update y j (S.partialD _ _)) (Joint.materialize _ (update g j f)) = _ * W.W _ (update y j x) (Joint.materialize _ (update g j (Reconstruction.direction _ _)))
  rw [← hu, ←hf,update_eq_self, update_eq_self,←Directional.product_deriv, Directional.W_deriv p he ht hw y (Joint.materialize _ g) j i]
lemma derivative (p:Fields.Euclidean T)(he:Y.Region T)(hw:Y.NonTangentialFree W)(ht:G.FullBody Y)(x:S.W)(f:Test4)(i:Axis):
   Z.starter W.symbol (S.partialD i x) f= -(if i=timeAxis then I else 1) • Z.starter W.symbol x (Reconstruction.direction i f):=by
  apply Z.buds; intro a; apply Z.splits; intro j
  simpa only [LinearMap.smul_apply,Z.sp,Z.actual, inner_smul_right,Z.bearings] using diff_expect p he hw ht (Sentence.rev j) a x f i

lemma unit_expect (h:S.System P)(p:Fields.Euclidean T)(he:Y.Region T)(hw:Y.NonTangentialFree W)(l r:Sentence S)(f:Test4): W.expect (l++(S.unit,f)::r)=(∫ x, f x)* W.expect (l++r):=by
  let j : Fin ((l.length+r.length)+1) := ⟨l.length,by omega⟩
  let w:= l++(S.unit,f)::r
  let q (i:Fin (l.length+r.length+1)):Letter S:= w.get (Fin.cast (by simp [w,Nat.add_assoc]) i)
  have hq: List.ofFn q=w:= by
    refine List.ext_get (by simp [w,Nat.add_assoc]) (fun k i ht=>?_)
    rw [List.get_ofFn];rfl
  have hx : q j=(S.unit,f):=by
    simp [q,j,w,List.getElem_append_right]
  have hL: List.ofFn (q ∘ j.succAbove)=l++r:=by
    rw [← Unary.ofFn_skip, hq]; simp [w, List.eraseIdx_append,j]
  let u : Fin (l.length+r.length+1)→S.W:=Prod.fst ∘ q
  let g := Prod.snd ∘ q
  change W.expect w = _
  rw [← hq,← hL,expect_ofFn,expect_ofFn,← show g j=f from congrArg Prod.snd hx]
  exact Unary.W_unit h p he hw u j (congrArg Prod.fst hx) g
lemma scalarUnit (h:S.System P)(p:Fields.Euclidean T)(he:Y.Region T)(hw:Y.NonTangentialFree W) (f: Test4): Z.starter W.symbol S.unit f=(∫ x,f x) • LinearMap.id := by
  apply Z.buds; intro i; apply Z.splits; intro j
  simp only [Z.sp,Z.actual,LinearMap.smul_apply,LinearMap.id_apply, inner_smul_right,Z.bearings]
  exact unit_expect h p he hw _ i f

end Soil
end YM.Massive.Bridge
