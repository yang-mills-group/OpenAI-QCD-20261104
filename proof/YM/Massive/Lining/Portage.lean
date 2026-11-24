import YM.Massive.Lining.Solar
/-!
Combine gauge and spin verification into genuine stencil comparisons (jets d). -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lining.Temper.Germ
open QCD QCD.Lat Lattice Wilson Massive.Papyrus UV Filter Function Finset Matrix Grass
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical Kronecker TensorProduct
open SourceRead Purl Scan Cylinder Paper TensorProduct Source.Drops
variable {H:Source.Hol su}{d:ℕ}(F:Flag H d (d/2))(U: Kedge H d (d/2))(t:Finset Cover)
local notation "Q" => SpinMode d
local notation "T" => Nearest t 6
local notation "D" => Cylinder.Formula t 6
variable (J:Labels.Jet su)
private lemma rproj (p:GPol) : Response d (fun h=> Labels.read (extraction F (zephyr (H:=H) J d h)) p) (fun h=> Labels.read (expand _ (dil J d h)) p) 0 := (zephyral J F.lens).vehicle (v:=fun p':Snap su (d/2)=> Labels.read (expand _ p') p) (Work.G05.snap_read_smooth ..) -- lean notes f
lemma keys_heat (v:Labels.Key su)(p:ℝ): Labels.coord (Source.scaleJet J (p^2)) v = (p:ℂ)^(2*Labels.generation v)*Labels.coord J v:=by unfold Source.scaleJet Labels.coord; simp only [map_smul,Finsupp.smul_apply, smul_eq_mul, Labels.generation, Complex.ofReal_mul, Complex.ofReal_pow,pow_mul]
private lemma xp (p d:ℕ)(h:d<p): Response d (fun x:ℝ=> (x:ℂ)^p) (fun _=>0) 0:=by
    have hv:Response d (fun x:ℝ=>x^p) (fun _=>0) 0:=by
       refine ⟨contDiffAt_id.pow _,contDiffAt_const,?_⟩; intro k hk; ext1; rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,iteratedDeriv_fun_pow_zero,if_neg (ne_of_lt (hk.trans_lt h))]; simp
    have ht:=hv.linear Complex.ofRealCLM; simp only [Complex.ofRealCLM_apply,Complex.ofReal_pow,map_zero] at ht; --
    exact ht
lemma keys_lens (v:Labels.Key su)(d:ℕ): Response d (fun h=> Labels.coord (expand _ (dil J d h)) v) (fun h=> Labels.coord (Source.scaleJet J (h^2)) v) 0 :=by
   let u(w:ℝ):=Labels.coord (expand _ (dil J d w)) v; by_cases hh:v.1<d/2-1
   · simp_rw [show ∀ x:ℝ, Labels.coord (expand _ (dil J d x)) v=Labels.coord (Source.scaleJet J (x^2)) v from fun x=> by simp [Labels.coord,dil,expand, trunk,hh]]; simp_rw [keys_heat]; exact Response.refl (( Complex.ofRealCLM.contDiff.contDiffAt.pow _).mul contDiffAt_const)
   simp_rw [show ∀ x:ℝ, Labels.coord (expand _ (dil J d x)) v=0 from fun x=> by simp [Labels.coord,expand,hh], keys_heat]
   have ht:= (xp (2*Labels.generation v) d (by unfold Labels.generation; omega)).product (Response.stature (Labels.coord J v) (0:ℝ)); simp only [zero_mul] at ht; exact ht.echo
lemma gauge_lens (p:GPol) : Response d (fun h=> Labels.read (extraction F (zephyr (H:=H) J d h)) p) (fun h=> Labels.read (Source.scaleJet J (h^2)) p) 0:=by
   refine (rproj F J p).trans ?_
   induction p using MvPolynomial.induction_on with
   | C a=> simp only [Labels.read,MvPolynomial.aeval_C, Algebra.algebraMap_self,RingHom.id_apply]; exact Response.stature _ _
   | add p q hp hq=>simp_rw [map_add]; exact hp.plus hq
   | mul_X p i hp=>simp_rw [map_mul]; refine hp.product ?_; simp only [Labels.read,MvPolynomial.aeval_X]; exact keys_lens J i d
abbrev ψear (x:ℝ) : SpinPol d→ₐ[ℂ]SpinPol d:= adapter (spool U t J x) (Mstar (spool U t J x))
abbrev slate (x:ℝ) (d:ℕ) : SpinPol d→ₐ[ℂ]SpinPol d:= Grass.adapter (SourceRead.scaled x) (SourceRead.scaled x)
lemma atom_lens (ht:box d⊆t)(i:Pairs Q): Response d (fun h=> ψear U t J h (atom i)) (fun h=> slate h d (atom i)) 0:=by
   unfold ψear slate adapter; simp_rw [change_atom]; apply Response.series; intro j _; refine Response.smuls ?_ (Response.stature (atom j) 0); rcases i with i|i <;> rcases j with j|j
   · exact reel_lens U t J ht i j
   · exact Response.stature (0:ℂ) _
   · exact Response.stature (0:ℂ) _
   exact reel_star U t J ht i j
lemma spin_lens (ht:box d⊆t)(y:SpinPol d): Response d (fun h=> ψear U t J h y) (fun h=> slate h d y) 0:=by
   induction y using ExteriorAlgebra.induction with
   | algebraMap a=> simp only [AlgHom.commutes]; exact Response.stature _ (0:ℝ)
   | ι v=> rw [line_atoms]; simp_rw [map_sum,map_smul]; exact Response.series _ _ _ (0:ℝ) (fun i _=> (Response.stature _ _).smuls (atom_lens U t J ht i))
   | add p q hp hq=>simp_rw [map_add]; exact hp.plus hq
   | mul p q hp hq=>simp_rw [map_mul]; exact hp.product hq
lemma desired_air(h:ℝ)(x:GPol)(y:SpinPol d): desired (x ⊗ₜ[ℂ] y) J h= Labels.read (Source.scaleJet J (h^2)) x • slate h d y:= by rw [desired,TensorProduct.map_tmul, TensorProduct.lid_tmul]; rfl
lemma wind_lens(ht:box d⊆t)(x:Pol d) : Response d (fun h=> let p:=intaglio t d h; adapter p p (glaze F U t (zephyr (H:=H) J d h) x)) (desired x J) 0:=by
   induction x using TensorProduct.induction_on with
   | zero=>
       have he: desired (0:Pol d) J=fun _=>0:=funext fun h=>by rw [desired,map_zero,map_zero]
       simp only [map_zero]; rw [he]; exact Response.stature (0:SpinPol d) (0:ℝ)
   | tmul x y=> have he:= (gauge_lens F J x).smuls (spin_lens U t J ht y); simp_rw [stencil,map_smul]; rw [funext fun h=> desired_air J h x y]; simp_rw [adapt_test]; exact he
   | add x y hx hy=> simp_rw [map_add]; rw [show desired (x+y) J=(fun h=> desired x J h+desired y J h) from funext fun h=>by rw [desired, map_add,map_add]; rfl]; exact hx.plus hy
lemma seed (ht:box d ⊆ t)(u: Pol d)(v:D)(h:∀ x:Land,porch t x v = glaze F U t x u) : SourceRead.Agrees (SourceRead.onStencil H v d J) (SourceRead.desired u J):=by
    have he:= (wind_lens F U t J ht u).smooth_compare; unfold onStencil; simp_rw [← porch_eval,h]; exact he
end YM.Massive.Lining.Temper.Germ
#print axioms YM.Massive.Lining.Temper.Germ.seed
