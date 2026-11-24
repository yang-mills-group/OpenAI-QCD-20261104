import YM.Massive.Lining.Zephyr
/-! # Forward UV-germ validation of common stencil.

Taylor snap(squared dilation). Don't identify truncated spin and gauge sample
with any exact section at finite h. Keep wt=d inclusive. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lining.Temper
open QCD QCD.Lat Lattice Wilson Massive.Papyrus UV Filter Function Finset Matrix Grass
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical Kronecker TensorProduct
open Purl Scan Cylinder Paper TensorProduct
variable {H:Source.Hol su}{d:ℕ}(F:Flag H d (d/2))(U: Kedge H d (d/2))(t:Finset Cover)
local notation "Q" => SpinMode d
local notation "T" => Nearest t 6
local notation "D" => Cylinder.Formula t 6
open SourceRead
namespace Germ
open Source.Drops
variable (J:Labels.Jet su)
def zephyr (d:ℕ)(h:ℝ):Land:= H.links (d/2) J (h^2)
def dil (d:ℕ)(h:ℝ):Snap su (d/2):= trunk (d/2) (Source.scaleJet J (h^2))
lemma scanned(h:ℝ)(d:ℕ): zephyr (H:=H) J d h=trunkJ (d/2) H (dil J d h):= scales H J _
lemma dil_home(d:ℕ): dil J d 0=0:=by funext i; simp [dil, trunk,Source.scaleJet]
lemma dil_tone (d:ℕ): ContDiffAt ℝ (d:ℕ∞) (dil J d) 0:=by apply contDiffAt_pi.mpr; intro i; change ContDiffAt _ _ (fun h:ℝ=> (h^2)^(i.val+2) • J i.val) _; exact glowE (i.val+2) (J i.val)
 where glowE {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](i:ℕ)(x:E): ContDiffAt ℝ (d:ℕ∞) (fun h:ℝ=> (h^2)^i • x) 0:= ((contDiffAt_id.pow 2).pow _).smul contDiffAt_const
lemma zephyral {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E] {f:Land→E}{g:Snap su (d/2)→E}
    (h: Response d (fun x=> f (trunkJ (d/2) H x)) g 0): Response d (fun x=>f (zephyr (H:=H) J d x)) (fun x=>g (dil J d x)) 0:=by
     simp_rw [scanned]; exact (Response.refl (dil_tone J d)).transit (v:=fun x=> f (trunkJ _ H x)) (v':=g) ((dil_home J d).symm ▸ h)
abbrev intaglio (d:ℕ)(h:ℝ):Matrix T (SpinMode d) ℂ:= SourceRead.spinLink h
lemma scoutL (p:Multi d)(x:Cover)(h:ℝ): SourceRead.profile p x h = (h:ℂ)^spinWeight p*(profileL p x:ℂ):=by rw [profile,Complex.ofReal_mul, Complex.ofReal_pow]; rfl
lemma spinFace (h:ℝ)(d:ℕ): intaglio t d h=nacre (fun x p=> profile p x.val h • 1):=by
    ext ⟨⟨i,a⟩,w⟩ ⟨⟨j,b⟩,v⟩; by_cases ht:a=b <;> by_cases hh:w=v <;> simp only [intaglio,spinLink,Matrix.of_apply,imprints, Matrix.smul_apply, Matrix.one_apply,smul_eq_mul] <;> simp [*]
lemma scout_star (h:ℝ)(d:ℕ): Mstar (intaglio t d h)=intaglio t d h:=by rw [spinFace,mark_star]; congr 1; funext x p; rw [mstar_smul,mstar_bulk]; simp [profile] -- star complex cast defeq?
lemma omen_face (h:ℝ)(d:ℕ) : scaled (d:=d) h = spar id (fun i=> ((h:ℂ)^spinWeight i) • 1):= (spar_dex (fun i=> (h:ℂ)^spinWeight i)).symm
lemma omen_star (h:ℝ)(d:ℕ) : Mstar (scaled (d:=d) h)=scaled h:=by rw [omen_face,spar_color]; congr 1; funext i; rw [mstar_smul,mstar_bulk]; simp
private lemma shake (x:Cover)(U: Kedge H d (d/2)): Response d (fun h=>U.T x (zephyr (H:=H) J d h)) (fun _ : ℝ=> (1:Mat)) 0 := zephyral J (U.germ x) -- g infer?
def emL (c:ℂ) : Mat→L[ℝ]Bundle:= LinearMap.toContinuousLinearMap
             { toFun:=fun x=> c • touch x,map_add':=by intro x y; rw [← touch_add,smul_add]
               map_smul':=by
                                            intro x y; suffices h: touch (x • y)= x • touch y by rw [h,smul_comm]; rfl
                                            unfold touch; ext i j; simp [Complex.real_smul]; ring }
private lemma sketch (p q:Multi d)(x : t) : Response d (fun h=> profile q x.val h • emboss U t (zephyr (H:=H) J d h) p x) (fun h=> profile q x.val h • ((sample p x.val:ℂ) • (1:Bundle))) 0:=by
     have hp:Response d (profile q x.val) (profile q x.val) 0:=Response.refl (f:=profile q x.val) (by unfold profile; exact (Complex.ofRealCLM.contDiff.contDiffAt).comp (0:ℝ) ((contDiffAt_id.pow _).mul contDiffAt_const)) 
     let φ:=emL (sample p x.val:ℂ); have he:= (shake J x.val U).linear φ; have hv:φ (1:Mat)=(sample p x.val:ℂ) • (1:Bundle):=congr_arg (fun M:Bundle=> (sample p x.val:ℂ) • M) touch_one; have H:Response d (fun h=> φ (U.T x.val (zephyr (H:=H) J d h))) (fun _=> (sample p x.val:ℂ) • (1:Bundle)) 0:=by rw [← hv]; exact he
     exact hp.smuls H
private lemma lobby(ht :box d⊆t) (p q:Multi d)(h:ℝ): (∑ x:↥t, profile q x.val h • ((sample p x.val:ℂ) • (1:Bundle))) = if p=q then ((h:ℂ)^spinWeight p) • 1 else 0:=by
    let B:=((h:ℂ)^spinWeight q); have he:(∑ x:↥t, profile q x.val h*(sample p x.val:ℂ))= B * (if p=q then 1 else 0):=by
         simp_rw [scoutL,mul_assoc,← mul_sum]; apply congr_arg (fun y=> B*y); simp_rw [← Complex.ofReal_mul]; rw [← Complex.ofReal_sum, Finset.sum_coe_sort (f:=fun i : Cover=> profileL q i*sample p i)]; simp_rw [mul_comm (profileL q _)]; rw [surveyor p q ht]; by_cases hp:p=q <;> simp [hp,eq_comm] -- look
    rw [show (∑ x:↥t, profile q x.val h • ((sample p x.val:ℂ) • (1:Bundle)))=(∑ x:↥t, profile q x.val h * (sample p x.val:ℂ)) • (1:Bundle) by simp_rw [Finset.sum_smul,mul_smul], he]; by_cases hp:p=q <;> simp [hp,B]
lemma asp (ht:box d⊆t)(p q: Multi d): Response d (fun h=>∑ x:↥t,emboss U t (zephyr (H:=H) J d h) p x*((profile q x.val h) • (1:Bundle))) (fun h=>if p=q then (h:ℂ)^spinWeight p • (1:Bundle) else 0) 0:=by
    simp_rw [Matrix.mul_smul, Matrix.mul_one,← lobby t ht]; exact Response.series _ _ _ _ (fun i _=>sketch U t J p q i)

private abbrev nth (i j: Fiber):Bundle→L[ℝ]ℂ:= LinearMap.toContinuousLinearMap { toFun:=fun x=>x i j, map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
abbrev spool (h:ℝ) : Matrix Q Q ℂ:= start U t (zephyr (H:=H) J d h)*intaglio t d h
lemma reel_lens (ht:box d⊆t)(i j:Q): Response d (fun h=> spool U t J h i j) (fun h => scaled h i j) 0:=by
    unfold spool start; simp_rw [omen_face, spinFace, spar,nacre_mul,imprints]; by_cases hh:i.2=j.2; swap; · simp only [if_neg hh]; exact Response.stature _ _
    simp only [if_pos hh, id_eq]; exact (asp U t J ht i.1.1 j.1.1).linear (nth i.1.2 j.1.2)
lemma reel_star (ht:box d⊆t)(i j:Q): Response d (fun h=> Mstar (spool U t J h) i j) (fun h=> scaled h i j) 0:=by
    let L:ℂ→L[ℝ]ℂ:=(starL' ℝ:ℂ≃L[ℝ]ℂ).toContinuousLinearMap; have he:= (reel_lens U t J ht i j).linear L; have hh (h:ℝ) : L (scaled h i j)= scaled h i j:= congr_arg (fun m:Matrix Q Q ℂ=> m i j) (omen_star h d); rw [funext hh] at he; exact he -- can infer
lemma adapt_test (x: ℝ)(y:SpinPol d) : Grass.adapter (intaglio t d x) (intaglio t d x) (ink U t (zephyr (H:=H) J d x) y)= Grass.adapter (spool U t J x) (Mstar (spool U t J x)) y:= by unfold ink spool; rw [adapt_together,mstar_mul,scout_star]
end Germ
end YM.Massive.Lining.Temper
#print axioms YM.Massive.Lining.Temper.Germ.reel_star
