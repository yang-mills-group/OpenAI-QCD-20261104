import YM.Massive.Papyrus.Pennant
/-! # Collecting common-stencil polynomials (real-linear normed space price). -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Papyrus.Paper
open Lattice Wilson RG Source Function QCD
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical
variable {E F V E' : Type*} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
  [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F][NormedAddCommGroup E'][NormedSpace ℝ E'][FiniteDimensional ℝ E']
  [NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V]
  {n:ℕ}
open Filter Work.G05 Work.G06 Finset
-- all forms on W
variable (s:Finset Cover)
def Plane (f:Land→F):= ∀ φ:F→ₗ[ℝ]ℂ, EntryPoly s (fun i=>φ (f i))
def Canvas (f:Land→F):= ∀ φ:F→ₗ[ℝ]ℂ, LP (fun i=>φ (f i))
variable {s}{f g: Land→E}{h:Land→F}
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma windup (φ:E→ₗ[ℝ]F)(h:Canvas f) : Canvas (fun x=> φ (f x)):=fun y=>h (y.comp φ)
lemma LPbridge {f:Land→ℂ}(hf:EntryPoly s f): Plane s f:=by
    intro φ; let c:=φ 1; let d:=φ Complex.I; have he(i:Land):φ (f i)= (f i).re • c + (f i).im • d:=by rw [← map_smul φ, ← map_smul φ,← map_add]; simp [Complex.real_smul]
    simp_rw [he,Complex.real_smul]; exact EPsum (EPprod (entryPoly_re hf) (EPconst c)) (EPprod (entryPoly_im hf) (EPconst d))
lemma CanLP {f: Land→ℂ}(hf:LP f):Canvas f:=fun t=>hf.mono (fun _ hi=> LPbridge hi t)
omit [FiniteDimensional ℝ E] in
lemma plane_sum {ι:Type*}(u:Finset ι) (f:ι→Land→E)(h:∀ i∈u,Plane s (f i)): Plane s (fun x=>∑ i∈u, f i x):=by intro p; simp only [map_sum]; exact EPseries u _ (fun i hi=> h i hi p)
omit [FiniteDimensional ℝ E] in
lemma plane_add (hf:Plane s f)(hg:Plane s g): Plane s (fun x=> f x+g x):=by intro p; simp only [map_add]; exact EPsum (hf p) (hg p)
omit [FiniteDimensional ℝ E] in
lemma Canvas.add (hf:Canvas f)(hg:Canvas g):Canvas (fun x=>f x+g x):=by intro p; simp only [map_add]; exact (hf p).add (hg p)
omit [FiniteDimensional ℝ E] in
lemma counting (e:E): Canvas (fun _=>e):= fun _=>fixLP _
private abbrev φ (V:Type*)[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V] (i:Fin (Module.finrank ℝ V)): V→ₗ[ℝ]ℝ:= (Module.finBasis ℝ V).coord i
private abbrev τ: ℝ→ₗ[ℝ]ℂ:= Complex.ofRealLI.toLinearMap
lemma street (ψ:E→ₗ[ℝ]ℂ)(y:E) : ψ y=∑ i, φ E i y • ψ (Module.finBasis ℝ E i):=by rw [show ∑ i,_= ψ (∑ i, φ E i y • Module.finBasis ℝ E i) by rw [map_sum]; simp only [map_smul]]; exact congr_arg ψ ((Module.finBasis ℝ E).sum_repr y).symm -- syntax ∑ _ rhs?
lemma planes (h:∀ i,EntryPoly s (fun x=>τ (φ E i (f x)))): Plane s f:=by
   intro p; conv=> arg 2; ext x; rw [street p (f x)]; skip
   simp only [Complex.real_smul]; exact EPseries _ _ (fun i _=> EPprod (h i) (EPconst _)) -- simp_rw street p infinite recursion
lemma Canvas.planes (hf:Canvas f) : ∀ᶠ i in atTop, Plane i f:= (eventually_all.mpr (fun i=> hf (τ.comp (φ E i)))).mono (fun _ hi=> Paper.planes hi)
omit [FiniteDimensional ℝ E] in
lemma depart (he:Plane s f): Canvas f:=fun φ=> current (he φ)
omit [FiniteDimensional ℝ E] in
lemma Canvas.sees (h: Canvas f): (u:Signed) → Canvas (fun i=>f (pull u 0 i)):=fun u φ=> (h φ).pull u
omit [FiniteDimensional ℝ E] in
lemma Canvas.odd (hf : Canvas f) : Canvas (fun i=>f (conjugate ∘ i)):=fun φ=>(hf φ).flip
omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ V] in
lemma Canvas.bilin (hf:Canvas f)(hg:Canvas h)(A:E→L[ℝ] F→L[ℝ] V): Canvas (fun i=>A (f i) (h i)):=by
    intro ψ; let B:=Module.finBasis ℝ E; have hh(i:Land) : ψ (A (f i) (h i))=∑ j, φ E j (f i) • ψ (A (B j) (h i)):=by
       conv_lhs=> rw [← B.sum_repr (f i)]
       simp only [map_sum, map_smul,_root_.sum_apply,smul_apply]; rfl
    rw [funext hh]; simp_rw [Complex.real_smul]; exact series _ _ (fun i _=> (hf (τ.comp (φ E i))).mul (hg (ψ.comp (A (B i)).toLinearMap)))
omit [FiniteDimensional ℝ E] in
lemma Canvas.annual {ι:Type*}(u:Finset ι) (f:ι→Land→E)(h:∀ i∈u,Canvas (f i)) : Canvas (fun x=>∑ i∈u, f i x):=by intro p; simp_rw [map_sum]; exact series _ _ (fun i hi=> h i hi p)
omit [FiniteDimensional ℝ E] in
lemma Canvas.scale (c:ℝ)(h:Canvas f): Canvas (fun i=> c • f i):= windup (c • LinearMap.id) h
omit [FiniteDimensional ℝ F] in
lemma multiline (d:ℕ)(L:Tensor.T E F d)(h:Canvas f): Canvas (fun i=>Tensor.diagonal L (f i)):=by
    induction d with
    | zero=> have ht(i:Land): Tensor.diagonal L (f i)= Tensor.diagonal L 0:= congr_arg L (Subsingleton.elim _ _); simp_rw [ht]; exact counting _ --
    | succ d ih=>
       let B:=Module.finBasis ℝ E; let Q(i: Fin (Module.finrank ℝ E)):=L.curryLeft (B i); let V:=fun i=> Tensor.diagonal (Q i)
       have h' (u:Land): Tensor.diagonal L (f u)=∑ i, φ E i (f u) • V i (f u):=by
          let x:=f u; change Tensor.diagonal L x=_; rw [show Tensor.diagonal L x=Tensor.diagonal (L.curryLeft x) x from congr_arg L (by ext1 k; refine Fin.cases ?_ (fun j=>?_) k <;> simp)]; let M:=fun i:Fin (Module.finrank ℝ E)=> φ E i x • Q i; have he: L.curryLeft x=∑ i,M i:=by nth_rw 1 [← B.sum_repr x]; simp only [map_sum,map_smul]; rfl
          rw [he,Tensor.diagonal,_root_.sum_apply]; rfl
       rw [funext h']; refine Canvas.annual _ _ (fun i _=>?_) ; exact Canvas.bilin (windup _ h) (ih (Q i)) (ContinuousLinearMap.lsmul ℝ ℝ (E:=F))
omit [FiniteDimensional ℝ F] in
lemma Canvas.swing {L:E→F}(n:ℕ)(h:Canvas f): Canvas (fun i=> blockTaylor n L (f i)):=by simp_rw [blockTaylor,Finset.sum_apply]; exact Canvas.annual _ _ (fun _ _=> multiline _ _ h)
lemma patternM {A:Land→su.Mat}(h:∀ i j, LP (fun x=>A x i j)) : Canvas A:=by
    intro φ; let f:=fun x=> φ (A x); let r:= Complex.reLm.comp φ; let y:= Complex.imLm.comp φ; have he(x:Land):φ (A x)=(r (A x):ℂ)+(y (A x):ℂ)*Complex.I:= (Complex.re_add_im (φ (A x))).symm
    simp_rw [he]; have H(ψ:su.Mat→ₗ[ℝ]ℝ): LP (fun x=> (ψ (A x):ℂ)) := (eventually_all.mpr (fun i=>eventually_all.mpr (h i))).mono fun i h=> entryPoly_functional ψ A h; exact (H _).add ((H _).mul (fixLP _))
lemma patternK (A:Land→Mat) (h:∀ i j, LP (fun x=>A x i j)) : Canvas A:=patternM h
lemma pattern (A:Land→Mat)(h:Canvas A)(i j:Hue): LP (fun x=> A x i j):=h ⟨ ⟨fun x=>x i j,fun _ _=>rfl⟩, fun _ _=>rfl⟩
lemma plane_color (A:Land→Mat)(h:Plane s A)(i j:Hue): EntryPoly s (fun x=> A x i j):=h ⟨ ⟨fun x=>x i j,fun _ _=>rfl⟩, fun _ _=>rfl⟩
end YM.Massive.Papyrus.Paper
#print axioms YM.Massive.Papyrus.Paper.Canvas.swing
