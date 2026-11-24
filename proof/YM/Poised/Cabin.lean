import YM.Poised.Aero
import YM.Poised.Arcs
/-!
# Booked spin-Ward mask cancellation; n-linear budgets across chart equality
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {J B : Type}{d a l k n:ℕ}{c:Side}
namespace Pipes
open Beacon Gem MultiNext.SignedSource YM.Next.Foundations
variable (T:Taper) (b:Cover) [Fintype B] {V:Support c}
local notation "C"=> su.Color
local notation "S"=> Flet B
local notation "Q"=> C × Flet B
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 800000
local instance : NormedSpace ℝ (Book c B d):=inferInstance
local instance : NormedSpace ℝ (Snap su d):= inferInstance
private lemma descends (f: Fin n→ Book c B d) (i: Edge (Site c)): (iteratedFDeriv ℝ n (enroll T b) 0 f).1 i=iteratedFDeriv ℝ n (logo (G:=su)) 0 (fun j=>mint b i (f j)):=by
   let L : Path c B →L[ℝ] C:= (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)
   change L (iteratedFDeriv ℝ n (enroll T b) 0 f)=_
   have ht := L.iteratedFDeriv_comp_left (seal_live T b (B:=B) (c:=c) (d:=d)) (i:=n) le_top
   have hu := jets_linear (mint (B:=B) b i (d:=d)) ((logo_smooth su (d/2)).of_le (m:=↑n) le_top)
   exact (DFunLike.congr_fun ht f).symm.trans (DFunLike.congr_fun hu f)
lemma finish_stitch (p:ℂ)(q: Fin n→ Q): iteratedFDeriv ℝ n scaleG 0 (fun i=>((q i).1,p • (q i).2))= p • iteratedFDeriv ℝ n scaleG 0 q:=by
    let L : Flet B →L[ℝ] Flet B:= p • (ContinuousLinearMap.id ℝ _)
    let U: Q →L[ℝ] Q:= (ContinuousLinearMap.id ℝ C).prodMap L; have hp:scaleG ∘ U=L ∘ scaleG:= funext fun i=>step_right ..
    have ht := jets_linear U (((scaleG_live (B:=B)).contDiffAt).of_le (m:=↑n) le_top)
    have he:= L.iteratedFDeriv_comp_left (scaleG_live.contDiffAt) (i:=n) (x:=(0:Q)) le_top
    exact DFunLike.congr_fun (ht.symm.trans (by rw [hp,he])) q
lemma treasures (X: Fin n→ Book c B d)(i:Site c): asks (iteratedFDeriv ℝ n (enroll T b) 0 X).2 i= spun T b i • iteratedFDeriv ℝ n scaleG 0 (fun j=>((X j).1 i,tags (X j).2.2 (vector (offset b i)))):=by
   let f:= scoring (d:=d) (B:=B) (c:=c) T b; obtain ⟨L,hL⟩:=scoring_cl T b (B:=B) (d:=d) (c:=c)
   let W: Path c B →L[ℝ]S := (askCL i).comp (ContinuousLinearMap.snd ℝ _ _)
   let Y: Book c B d→L[ℝ] Q:= ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)).prod ((askCL i).comp (L.comp ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))))
   have hx(x) : Y x=(x.1 i, spun T b i • tags (x.2.2) (vector (offset b i))):=by rw [← imprint T b x.2.2 i, ← hL]; rfl
   have hp : scaleG ∘ Y=W ∘ enroll T b:=by
      funext x; rw [Function.comp_apply,hx x,← imprint]; exact (hailF (sealsZ x.1) (scoring T b x.2.2) i).symm
   have hu := jets_linear Y (((scaleG_live (B:=B)).contDiffAt).of_le (m:=↑n) le_top)
   have hW := W.iteratedFDeriv_comp_left (seal_live T b (c:=c) (d:=d) (B:=B)) (i:=n) le_top
   rw [hp] at hu
   change W (iteratedFDeriv ℝ n (enroll T b) 0 X)=_; apply Eq.trans (DFunLike.congr_fun (hW.symm.trans hu) X); change iteratedFDeriv ℝ n scaleG 0 (fun j=>Y (X j))=_; simp_rw [hx]; exact finish_stitch (B:=B) (spun T b i) (fun j=> ((X j).1 i,tags (X j).2.2 (vector (offset b i))))
lemma share (u: Fin n→ℕ):∑ i,u i/2 ≤ (∑ i,u i)/2:=by
    apply Nat.le_div_iff_mul_le (by norm_num : 0< (2:ℕ)) |>.mpr; rw [sum_mul]; exact sum_le_sum fun i _=> Nat.div_mul_le_self ..
structure Burst (X: Book c B d)(V:Support c)(b:Cover)(w:ℕ) : Prop where
    W : ∃ f:E4→C, f∈rangeLt C (w/2+1) ∧ ∀ i∈V, f (vector (offset b i))=X.1 i
    H : throughSlot X.2.1 (w/2)
    S0 : ∀ p, w < spinWeight p → X.2.2 p=0
structure Buoyant (X: Path c B)(V:Support c)(b:Cover)(w:ℕ): Prop where
    H : ∃ f:Potential su, f∈rangeLt (Axis→C) (w/2) ∧ ∀ i,Mom.needed V i→ X.1 i=f (vector (offset b i.1)) i.2
    S0: ∃ f:E4→S,f∈rangeLt S ((w-1)/2) ∧ ∀ i ∈V,asks X.2 i=frond b i • f (vector (offset b i))
variable (hx : Nonwrapping V (wrap c b)) (ht:100 ≤ c.val)
include hx ht
lemma ordinance (X : Fin n → Book c B d)(w : Fin n → ℕ)(h:∀ i,Burst (X i) V b (w i))(hv : ∀ i, 2 ≤ w i) : Buoyant (iteratedFDeriv ℝ n (enroll T b) 0 X) V b (∑ i,w i):=by
   choose f hf hh using fun i=> (h i).W; let u i:=w i/2; have hu i:0 < u i:=by unfold u; have:=hv i; omega
   constructor
   · let q (x : E4)(i : Axis):= iteratedFDeriv ℝ n logo (0: EdgeRead su (d/2)) fun j=> (f j x,Place.jump (f j) x i,Place.road x i (X j).2.1)
     refine ⟨q, grows _ (share w) (show q∈ rangeLt (Axis→C) (∑ i,u i) from vector_band _ fun i=>logo_cost _ f _ u i hu hf fun i=> (h i).H),fun i hi=>?_⟩
     unfold q; rw [descends]; apply congr_arg; funext j; unfold Place.jump
     change ((X j).1 i.1, (X j).1 i.1-(X j).1 (i.1+Lattice.step i.2),Place.road _ _ _) = (_,_ ,_)
     rw [hh j i.1 hi.1,show vector (offset b i.1)+basis i.2= vector (offset b (i.1+Lattice.step i.2)) from ?_,hh j _ hi.2]; rotate_left
     · rw [lastX b hx ht i hi]; exact (Place.seat_add .. |>.trans (congr_arg (Place.seat (offset b i.1)+ ·) (Place.seat_step ..))).symm
     rfl
   let p i:= tags (X i).2.2
   refine ⟨_,scaleG_cost n w f p hf (fun i=>tall (X i).2.2 (n:=(w i-1)/2) fun j he=> (h i).S0 j (by unfold spinWeight; have := hv i; omega)),fun i hi=> ?_⟩
   rw [treasures T b X i, fronds T b hx ht i hi]; unfold p; simp only [hh _ i hi]
structure Glazed (X Y: Path c B)(V:Support c):Prop where
    H : ∀ i,Mom.needed V i → X.1 i=Y.1 i
    S0 : ∀ i ∈ V, asks X.2 i=asks Y.2 i
lemma issued (X: Path c B)(w:ℕ)(hk:w≤d)(h: Buoyant X V b w): ∃ Y: Book c B d,Burst Y V b w ∧ Glazed X (fderiv ℝ (enroll T b) 0 Y) V:=by
    obtain ⟨⟨f,hf,hW⟩,A,hA,h⟩:=h; obtain ⟨W,Z,hV,hZ,rfl⟩:=generated (G:=su) f hf (by omega : w/2 ≤ d/2); obtain ⟨Y,rfl,hy⟩:=served hA (show (w-1)/2 ≤ d+1 by omega)
    let R:Book c B d:=((fun i=> W (vector (offset b i))),Z,Y)
    refine ⟨R,⟨⟨W,hV,fun i _=>rfl⟩,hZ,fun p hv=> hy p (by unfold spinWeight at hv; omega)⟩,?_⟩
    constructor; swap; · intro i hi; have hp:=treasures T b (fun _:Fin 1=>R) i; rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply, scaleG_first, fronds T b hx ht i hi] at hp; exact (h i hi).trans hp.symm
    intro i hi; have hp:=descends T b (fun _:Fin 1=>R) i; rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply,Place.echoing] at hp; rw [hp,hW i hi]; change (W (vector _) - W (vector _+basis i.2))+Place.steady _=Place.steady _+(W (vector _) - W (vector _)); rw [lastX b hx ht i hi]; rw [show vector (offset b i.1 + Lattice.step i.2)=vector (offset b i.1)+ basis i.2 from (Place.seat_add .. |>.trans (congr_arg _ (Place.seat_step ..)))]; exact add_comm ..
end Pipes
end YM.Massive.Poised
