import YM.Massive.Papyrus.Retort
/-! # Spatial polynomials on the cover and switch/charge actions.

LP uses positive links and conjugates over true neighborhoods of the root,
w/meta-support bound. Name a common S before using them in calibration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Papyrus
open Lattice Wilson RG Source Function QCD
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical
variable {E F V E' : Type*} [NormedAddCommGroup E][NormedSpace ℝ E]
  [NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup E'][NormedSpace ℝ E']
  [NormedAddCommGroup V][NormedSpace ℝ V]
  {n:ℕ}
open Filter Work.G05 Work.G06 Finset
abbrev Land:=CoverConfig su
namespace Paper
variable {f g: Land→ℂ}{u:Finset Cover}
lemma ofGen {S T:Finset Cover}(G: Gauge)(r:CoverConfig G→CoverConfig G)(f:CoverConfig G→ℂ)(he: EntryPoly S f) (h:∀ i: Index G S, EntryPoly T (fun x=> Source.entry (r x) i)): EntryPoly T (fun x=>f (r x)):=by
    obtain ⟨p,H⟩:=he; suffices φ:EntryPoly T (fun x=>MvPolynomial.aeval (Source.entry (r x)) p) by simp_rw [← H]; exact φ
    clear f H; unfold EntryPoly at h; choose Q θ using h
    refine ⟨MvPolynomial.aeval Q p,fun x=>?_⟩; let F:Source.Formula G T→ₐ[ℂ]ℂ:=MvPolynomial.aeval (Source.entry x (S:=T)); have he:F.comp (MvPolynomial.aeval Q)=MvPolynomial.aeval (Source.entry (r x)):=by ext i; rw [AlgHom.comp_apply,MvPolynomial.aeval_X,MvPolynomial.aeval_X]; exact θ i x
    exact DFunLike.congr_fun he p
lemma limb (i:Index su u): EntryPoly u (fun x:Land=>Source.entry x i):= ⟨MvPolynomial.X i,fun _=>MvPolynomial.aeval_X ..⟩
lemma spread (h: EntryPoly u f){v: Finset Cover}(hu: u ⊆ v) : EntryPoly v f:= ofGen su id f h (fun i=> limb (⟨i.1.val,hu i.1.property.1,hu i.1.property.2⟩,i.2))
lemma EPsum (hf:EntryPoly u f)(hg:EntryPoly u g) : EntryPoly u (fun x=>f x+g x):=by obtain ⟨p,hp⟩:=hf; obtain ⟨q,hq⟩:=hg; exact ⟨p+q,fun x=> by rw [_root_.map_add,hp,hq]⟩
lemma EPprod (hf:EntryPoly u f)(hg:EntryPoly u g): EntryPoly u (fun x=> f x*g x):=by obtain ⟨p,hp⟩:=hf; obtain ⟨q,hq⟩:=hg; exact ⟨p*q,fun x=>by rw [_root_.map_mul,hp,hq]⟩
lemma EPconst (p:ℂ): EntryPoly u (fun _:Land=>p):= ⟨MvPolynomial.C p,fun _=>by simp⟩
/-- Common neighborhood not named yet. -/
def LP (f:Land→ℂ):= ∀ᶠ u in atTop, EntryPoly u f
lemma current (h:EntryPoly u f):LP f:=by filter_upwards [eventually_ge_atTop u] with i hi; exact spread h hi
lemma LP.gen (hf:LP f)(r:Land→Land)(h:∀ (u: Finset Cover)(i:Index su u),LP (fun x=>Source.entry (r x) i)): LP (fun x=> f (r x)):=by
   obtain ⟨u,hb⟩:=hf.exists
   haveI: Finite (UsedEdges u):=Finite.of_injective (fun i:UsedEdges u=> ((⟨i.val.1,i.property.1⟩:↥u),i.val.2)) (fun i j h=> Subtype.ext (Prod.ext (congr_arg (Subtype.val ∘ Prod.fst) h) (congr_arg (Prod.snd (α:=↥u)) h)))
   have hh:= eventually_all.mpr (h u); filter_upwards [hh] with i hi; exact ofGen su r f hb hi
lemma LP.add (hf:LP f)(hg:LP g): LP (fun x=>f x+g x):=hf.mp (hg.mono fun _ he ht=>EPsum ht he)
lemma LP.mul (hf:LP f)(hg:LP g): LP (fun x=>f x*g x):=hf.mp (hg.mono fun _ he ht=>EPprod ht he)
lemma EPneg (hf:EntryPoly u f): EntryPoly u (fun x=> -(f x)):=by simpa only [neg_one_mul] using EPprod (EPconst (-1)) hf
lemma EPseries {ι: Type*} (v: Finset ι)(f:ι→Land→ℂ)(h:∀ i∈v,EntryPoly u (f i)) : EntryPoly u (fun x=>∑ i∈v,f i x):=by
   induction v using Finset.induction_on with
   | empty=>simpa only [sum_empty] using EPconst (u:=u) 0
   | @insert a v ha ih=> simp_rw [sum_insert ha]; exact EPsum (h _ (mem_insert_self ..)) (ih fun i hi=> h i (mem_insert_of_mem hi))
lemma fixLP (x:ℂ): LP (fun _:Land=>x):= Eventually.of_forall (fun _=>EPconst _)
lemma LP.bar (hf:LP f): LP (fun x=> star (f x)):=hf.mono fun _ h=> entryPoly_conj h
lemma series {ι:Type*}(f:ι→Land→ℂ)(u:Finset ι)(h:∀ i∈u, LP (f i)): LP (fun x=>∑ i∈u, f i x):=by
    have he:= (eventually_all_finset u).mpr h; exact he.mono (fun _=> EPseries u f)
lemma LP.neg (hf:LP f): LP (fun x=> -f x):=hf.mono fun _ h=> EPneg h
lemma point (i:Edge Cover)(a b:Fin su.repDim): LP (fun x:Land=> su.mat (x i) a b):= current (limb (u:={i.1,i.1+step i.2}) (⟨i,by simp⟩,a,b,false))
lemma EPcolor {m : Land→su.El} (h: Work.G06.GP u m) (a b: Hue) : EntryPoly u (fun x=> Lat.colour (m x) a b):= h a b
lemma traveling (w:Walk)(x:Cover)(i j:Fin su.repDim): LP (fun U:Land=> su.mat (travel U x w) i j):=by
   induction w generalizing x i j with
   | nil=> exact fixLP _
   | cons r w ih=>
       simp only [travel,su.mat_mul,Matrix.mul_apply]; refine series _ _ (fun k _ => LP.mul ?_ (ih _ k j)); unfold Step.read; split; · simp only [su.mat_inv, Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]; exact (point _ k i).bar
       exact point _ i k
lemma LP.pull {f:Land→ℂ}(hf:LP f)(s:Signed) : LP (fun x=> f (Lattice.pull s 0 x)):=by
   have ht (i:Edge Cover)(a b : Fin su.repDim): LP (fun x:Land=>su.mat (Lattice.pull s 0 x i) a b):=by
      unfold Lattice.pull Step.read; split; · simp only [su.mat_inv, Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]; exact (point _ b a).bar
      exact point _ a b
   apply hf.gen; rintro u ⟨i,a,b,c⟩; unfold Source.entry; split; exact (ht i.val a b).bar; exact ht i.val a b
lemma LP.flip {f:Land→ℂ}(hf:LP f) : LP (fun x=>f (conjugate ∘ x)):=by
   have ht (i:Edge Cover)(a b:Fin su.repDim): LP (fun x:Land=>su.mat (conjugate (x i)) a b):=(point i a b).bar
   apply hf.gen; rintro u ⟨i,a,b,c⟩; unfold Source.entry; split; exact (ht i.val a b).bar; exact ht i.val a b
end Paper
end YM.Massive.Papyrus
#print axioms YM.Massive.Papyrus.Paper.LP.flip
