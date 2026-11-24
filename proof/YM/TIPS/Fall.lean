import YM.Patria.Orchid
/-! # transport from intermediate insertion onto genuine Tally measure. For ensembles. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Depth
open Set Filter Function Finset Lattice
open scoped ContDiff Topology BigOperators Classical
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory
open TorusPCAC.Geometry Exposure Rolls
variable {S:Scheme}{r:Side}{N d T:ℕ}
variable (A:Run S N r 6)(hA:A.Actual)
local notation "G"=>S.side r
abbrev relay (i:ℕ):=S.toStop r A.β A.w (F:=6) T i -- T binder force
variable {i j k:ℕ} (Y:Cover→ Insertion (S.side r T) 6)(u:Averaging)(b:Cover) (X:Insertion (S.side r T) 6)
abbrev report (i:ℕ)(b:Cover): Insertion (G i) 6:= relay A i (visitor S T i u b Y)
local notation "Vx"=> report A Y u
lemma stepped (hi:i < T): ⇑(relay A i X)=A.block i (relay A (i+1) X):=by unfold relay; rw [S.next r _ _ hi]; rfl
lemma arrivesHere: Vx T b=Y b:=by unfold report relay visitor; rw [S.entrance,centreN,one_smul,roles,chain_zero]; rfl
lemma rapid (h:∀ a b,march b ⇑(Y a)= Y (a+b))(hi:i≤T):∀ a b,march b (Vx i a)= Vx i (a+b):=by
     have hp :∀ (Y Y':Insertion (S.side r T) 6)(b:Cover) (i:ℕ)(hi:i≤T), march (ratioTo S T i • b) Y=Y' → march b (relay A i Y)=relay A i Y':=by
         intro U V b i hi h; induction hi using Nat.decreasingInduction generalizing b with|self=> unfold relay; rw [S.entrance]; simpa [centreN] using h|of_succ m hi ih => rw [stepped A _ hi,stepped A _ hi,step_shift A m b _ (ContinuousMap.continuous _),ih]; rwa [step_factor hi,Nat.mul_comm,mul_smul] at h
     intro a b; apply hp _ _ _ _ hi; unfold visitor; rw [smul_add]; exact trail Y u _ _ h
lemma placards {I:Type}[Fintype I](p:I→ℝ)(t:I→ Cover)(hi:i<T)(hf:∀ (v: Cover→ Insertion (S.side r T) 6)(b:Cover), Averaging.filter u (S.step i).L.val v b=∑ j,p j • v (b+t j)): ⇑(Vx i b)=∑ j,(p j:ℂ) • A.block i (Vx (i+1) ((S.step i).L.val • b+t j)):=by
     unfold report; rw [visit_eq Y u b p t hi hf,map_sum]; funext v; rw [ContinuousMap.sum_apply,Finset.sum_apply]; refine Finset.sum_congr rfl fun j _=>?_; let R:=visitor S T (i+1) u ((S.step i).L.val • b+t j) Y; rw [show relay A i (p j • R)=(p j) • relay A i R from map_smul ((relay A i).restrictScalars ℝ) _ R]; exact congr_arg ((p j:ℂ) • ·) (congr_fun (stepped A R hi) v)
-- Universal recipe at all X. prevents dependence on era lengths.V. choose from Finsupp
section
variable {W:Type}[AddCommGroup W][Module ℝ W] {m:ℕ} {I:Type} [Fintype I]
variable (p:I→ℝ)(t:I→ Cover)
def Fans (u:Averaging)(m:ℕ)(p:I→ℝ)(t:I→ Cover) : Prop:= ∀ (x: Cover→ Cover→₀ℝ)(b:Cover), Averaging.filter u m x b= ∑ i,p i • x (b+t i)
lemma ticket (h:Fans u m p t) (y:Cover→W) (b:Cover): Averaging.filter u m y b=∑ i,p i • y (b+t i):=by
     let L:= Finsupp.linearCombination ℝ y; let f(b:Cover):Cover→₀ℝ:=Finsupp.single b 1; have hx:=congr_arg L (h f b); rw [map_sum,roles,rollLinear] at hx; have ht:b=b:=rfl; simp_rw [map_smul, show ∀ b, L (f b)=y b from fun b=>(by simp [L,f])] at hx; rw [roles]; exact hx -- Fins recursion
end
-- each town may in own alignment.Canvas only cares shared ownership.K
structure AxisF (i:ℕ)(X:∀ i:ℕ,Cover→Insertion (S.side r i) 6) : Prop where
    trans(a b:Cover): march a (X i b)=X i (b+a)
structure TideT (T:ℕ)(X:∀ i:ℕ,Cover→Insertion (S.side r i) 6) : Prop where
    moves (i:ℕ)(h:i≤ T): AxisF (S:=S) (r:=r) i X
    steps (i:ℕ)(hi:i<T) (p:Type)[Fintype p](w:p→ℝ)(x:p→ Cover)(h:Fans u (S.step i).L.val w x) (b:Cover): ⇑(X i b)=∑ j,(w j:ℂ) • A.block i (X (i+1) ((S.step i).L.val • b+x j))
variable (B: Cover→ Insertion (S.side r N) 6)
lemma stampF (h:∀ a b,march b ⇑(Y a)= Y (a+b)) : TideT A u T Vx:=⟨fun _ hi=>⟨fun a b=> rapid A Y u h hi b a⟩,fun i h _ _ w x hz b=> placards A Y u b w x h (ticket u w x hz)⟩
include hA
lemma wingG (h:T≤N)(hp:∀ a b,march b (B a)= B (a+b)) : TideT A u T (trolley A B u):=⟨fun i hi=> ⟨fun a b=> axial A hA B u hp a b (hi.trans h)⟩,fun i hi _ _ w x hz b=> trailer A B u b w x (hi.trans_le h) (ticket u w x hz)⟩
omit hA
lemma tideDiff (X Y:∀ i:ℕ,Cover → Insertion (S.side r i) 6)(hp:TideT A u T X)(h:TideT A u T Y) : TideT A u T (X-Y):=by
    constructor; · intro i hi; refine ⟨fun a b=> funext fun V=> Eq.trans (map_sub (crank 1 1 (wrap _ a) (heat a)) _ _) (congr_arg₂ (·-·) (congr_fun ((hp.moves i hi).trans a b) V) (congr_fun ((h.moves i hi).trans a b) V))⟩
    intro i hi p _ w x hz b
    let f(j:p):= X (i+1) ((S.step i).L.val • b+x j); let g(j:p):=Y (i+1) ((S.step i).L.val • b+x j)
    have hh(j:p): A.block i (f j-g j)= A.block i (f j)- A.block i (g j):= congr_arg DFunLike.coe (map_sub (S.send r A.β A.w i) _ _) -- Π reduction.Texture
    change (⇑(X i b):Density _ 6)-⇑(Y i b)=_; rw [hp.steps _ hi p w x hz b,h.steps _ hi p w x hz b,← sum_sub_distrib]; exact Finset.sum_congr rfl (fun i _=> (smul_sub (w i:ℂ) _ _).symm.trans (congr_arg _ (hh i).symm))
end YM.Massive.Patria.Depth
#print axioms YM.Massive.Patria.Depth.tideDiff
#print axioms YM.Massive.Patria.Depth.ticket
#print axioms YM.Massive.Patria.Depth.stampF
