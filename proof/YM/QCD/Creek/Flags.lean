import YM.QCD.Creek.Horizon
/-! # Merge across disjoint decorated supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Creek.Stays
open Function Set Filter Ledge Grass NormedSpace
open scoped Topology BigOperators ContDiff Classical
variable {A M J ι: Type*} [Fintype A] [Fintype M] {p:ℝ} {U V X:Finset A} {x y:Alg A}{F G: EndA A}
lemma evenPay (h : Stays F U) (ht:Plus x): Plus (F x):=by change paint A (F x)=_; exact (DFunLike.congr_fun h.evenG.symm.eq x).trans (congr_arg F ht)
lemma paysR (h:Stays F U)(hv:Stays G V)(hp:Disjoint U V)(hx:x∈region U)(hy:y∈region V)(he:Plus x)(hy':Plus y): (F*G) (x*y) = F x * G y:=by
   have hm:Commute G (rightP x):= hv.parts hp x hx; rw [(he.central y).symm.eq]; change F (G _)=_; rw [show G (y*x)=G y*x from DFunLike.congr_fun hm.eq y,(he.central (G y)).eq]; have ht := h.parts hp.symm _ (hv.keeps (Finset.Subset.refl V) y hy); exact DFunLike.congr_fun ht.eq x
lemma heel (h:Stays F U)(hv:U⊆V): Stays F V :=⟨h.evenG,fun _=> h.keeps (hv.trans ‹_›),fun D=> h.parts (Disjoint.mono_right hv D)⟩
lemma paidI (U: Finset A) : Stays 1 U:=⟨Commute.one_left _,fun _ _ h=>h,fun _ _ _=>Commute.one_left _⟩
lemma paidO (U: Finset A) : Stays 0 U:=⟨Commute.zero_left _,fun {X} _ _ h=> (region X).zero_mem,fun _ _ _=>Commute.zero_left _⟩
lemma paysM (h:Stays F U)(hP:Stays G U):Stays (F*G) U:=⟨h.evenG.mul_left hP.evenG, fun hk y hy=> h.keeps hk _ (hP.keeps hk y hy),fun hx x hg=> (h.parts hx x hg).mul_left (hP.parts hx x hg)⟩
lemma paysD (h : Stays F U)(hP : Stays G U):Stays (F-G) U:=⟨h.evenG.sub_left hP.evenG,fun {X} h' x hv=>(region X).sub_mem (h.keeps h' x hv) (hP.keeps h' x hv),fun hp x he=> (h.parts hp x he).sub_left (hP.parts hp x he)⟩
lemma shine (F: ι→ EndA A)(p:Finset ι)(h:∀ i∈p,Stays (F i) U): Stays (∑ i∈p,F i) U:=by
   refine ⟨(finiteComm _ _ fun i hi=> (h i hi).evenG.symm).symm,fun {X} hh x hp=>?_,fun hh x hx=> (finiteComm _ _ fun i hi=> ((h i hi).parts hh x hx).symm).symm⟩
   rw [ContinuousLinearMap.sum_apply]; exact Subalgebra.sum_mem _ fun i hi=> (h i hi).keeps hh _ hp
lemma pumps (h:Stays F U)(p:ℂ): Stays (p • F) U:=⟨(timesComm h.evenG.symm p).symm,fun {X} hh x hx=> (region X).smul_mem (h.keeps hh _ hx) _,fun hp x hx=> (timesComm (h.parts hp x hx).symm p).symm⟩
lemma pile (h : Stays F U)(m:ℕ): Stays (F^m) U:=by induction m with
  | zero=>rw [pow_zero]; exact paidI _
  | succ m ih=> rw [pow_succ]; exact ih.paysM h
local instance {A:Type*}[Fintype A] : NormedAlgebra ℚ (EndA A):=.restrictScalars ℚ ℂ _
lemma Shut (U:Finset A): IsClosed (region U:Set (Alg A)) := by
  let Z : Submodule ℂ (Alg A):= (region U).toSubmodule; exact Submodule.closed_of_finiteDimensional Z
lemma tab (V:Finset A) {f : ℕ→Alg A}(hp:HasSum f x)(hx:∀ i, f i ∈ region V) : x∈region V:=by
  change x∈(region V:Set (Alg A)); apply (Shut V).mem_of_tendsto (f:=fun i:Finset ℕ=>∑ j∈i,f j) (b:=atTop) hp; exact Eventually.of_forall fun i:Finset ℕ=> Subalgebra.sum_mem (region V) (fun j _=> hx j)
lemma birther (F:EndA A)(x:Alg A) : HasSum (fun i:ℕ=> ((((i.factorial:ℂ)⁻¹) • F^i):EndA A) x) (birth F x):=by
  let f (i:ℕ): EndA A:= (i.factorial:ℂ)⁻¹ • F^i
  have hv: HasSum f (birth F) := exp_series_hasSum_exp' F
  let Q:= ContinuousLinearMap.apply ℂ (Alg A) x; have hu:= Q.hasSum hv
  change HasSum (fun i=>f i x) (birth F x); exact hu
lemma born_keeps (h : Stays F U)(hh:U⊆X)(x:Alg A)(hp:x∈region X): birth F x∈region X:=by
  let f (i:ℕ):EndA A:= (i.factorial:ℂ)⁻¹ • F^i
  have he : ∀ i:ℕ,f i x ∈ region X:= fun i=> ((Stays.pumps (h.pile i)) ((i.factorial:ℂ)⁻¹)).keeps hh x hp
  exact tab (x:=birth F x) X (birther F x) he
lemma birthP (h : Stays F U): Stays (birth F) U where
  evenG:=Commute.symm (roundP h.evenG.symm)
  keeps hh x hx:= born_keeps h hh x hx
  parts hh x hx:=(roundP (h.parts hh x hx).symm).symm
lemma sunset (h : Stays F U): Stays (excess F) U:= h.birthP.paysD (paidI U)

lemma ink (K:Matrix M M ℂ)(f:Pairs M ↪ A)(h: ∀ i j,K i j≠ 0 →pet f i∈U∧met f j∈U): Stays (excess (pond f K)) U:=by
   apply Stays.sunset; apply Stays.shine; intro i _; apply Stays.shine; intro j _; by_cases he:K i j=0
   · erw [he, zero_smul ℂ (Creek.v (met f j)*Creek.v (pet f i))]; exact paidO _
   exact (gammaT (h _ _ he).2 (h _ _ he).1).pumps _
lemma sunray [Fintype J] (K: Matrix M J ℂ) (u:M↪A)(v:J ↪ A) (h: ∀ i j,K i j≠0 → u i∈U ∧ v j∈U): Stays (excess (barkG u v K)) U:=by
   apply Stays.sunset; apply Stays.shine; intro i _; apply Stays.shine; intro j _; by_cases he:K i j=0
   · erw [he, zero_smul ℂ (l (v j)*Creek.v (u i))]; exact paidO _
   exact (gammaL (h _ _ he).2 (h _ _ he).1).pumps _
end YM.QCD.Creek.Stays
