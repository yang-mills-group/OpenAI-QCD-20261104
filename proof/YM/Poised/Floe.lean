import YM.Poised.Pipes
--import YM.MassiveQCD.Lyre.Gleam
/-!
# Spin readout ALWAYS lifted with the input phase. Position variables at actual UV horizon. Mixed-grade calibration used to promote to vanishing. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {J B : Type}{d a l k n:ℕ}{c:Side}
namespace Pipes
open Beacon Gem
variable (T:Taper) (b:Cover) [Fintype B] {V:Support c}
local notation "Ψ"=> Faces (Site c)
abbrev chain (T:Taper)(b:Cover)(t:ℝ) (d:ℕ): Matrix (Faces (Site c)) (Faces (UV.Multi d)) ℂ:= Matrix.fromBlocks (glow (d:=d) T b t) 0 0 (glow T b t)
def scoring (X:Lugs d B) : VectorD (Site c) B := let u:Matrix _ _ ℂ:= flats X; chain T b 1 d * u
lemma scion (x:Site c)(i j:Shell)(t:ℝ)(p:UV.Multi d): chain T b t d ((stretch _) (x,i)) ((stretch _) (p,j))= if i=j then spun T b x*profile p (offset b x) t else 0:=by
   cases i <;> cases j <;> simp only [chain, stretch,Equiv.coe_fn_mk,Sum.elim_inl,Sum.elim_inr, Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₂₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₁₂, Beacon.glow, Matrix.of_apply]; all_goals first | (simp only [reduceCtorEq, Matrix.zero_apply]; simp) | rfl | (simp [Prod.ext_iff,and_comm]) -- eta
lemma imprint (X:Lugs d B)(x:Site c) : asks (scoring T b X) x=spun T b x • tags X (vector (offset b x)):=by
   funext i j; unfold asks; unfold scoring; rw [Matrix.mul_apply, ← Equiv.sum_comp (stretch (UV.Multi d)), Fintype.sum_prod_type (α₁:=UV.Multi d)]
   simp_rw [scion]; simp only [Pi.smul_apply,smul_eq_mul,tags,Finset.sum_apply,Finset.mul_sum]; refine Finset.sum_congr rfl fun p _=>?_ ; rw [Finset.sum_eq_single i]
   · rw [if_pos rfl,show profile p _ 1= (score p (Place.seat (offset b x)):ℂ) from ?_,mul_assoc]; rotate_left
     · unfold profile score; simp
     have ht :flats X ((stretch _) (p,i))=X p i:=congr_fun (congr_fun (invers X) p) i; rw [ht]; rfl -- smul eq real
   · intro q _ hq; rw [if_neg (Ne.symm hq),zero_mul]
   simp
lemma scoring_cl : ∃ L : Lugs d B →L[ℝ] VectorD (Site c) B, ⇑L=scoring T b:=by
   refine ⟨LinearMap.toContinuousLinearMap { toFun:= scoring T b,map_add':=?_,map_smul':=?_ },rfl⟩
   · intro x y; apply flat_ext; intro i; change asks (scoring T b _) _=asks (scoring T b x) i+ asks (scoring T b y) i; rw [imprint, imprint,imprint]; unfold tags; simp [smul_add,sum_add_distrib]
   intro r x; apply flat_ext; intro i; change asks (scoring T b _) _=r • asks (scoring T b x) i; rw [imprint,imprint]; unfold tags; simp [smul_comm r,Finset.smul_sum]
variable (B d)
abbrev Marker:= Ln d × Lugs d B
 --
variable {B d}
abbrev Choir (d:ℕ):=Fin (d/2-1)⊕UV.Multi d
local instance : NormedSpace ℝ (Marker B d) := inferInstance
variable (B d)
private noncomputable def part (i: Choir d) : Marker B d→L[ℝ]Marker B d := LinearMap.toContinuousLinearMap {
  toFun:= fun x=>Sum.elim (fun j=>(Pi.single j (x.1 j),0)) (fun j=>(0,Pi.single j (x.2 j))) i,map_add':=by intro x y; cases i <;> simp [Pi.single_add],map_smul':=by intro r x; cases i <;> simp [Pi.single_smul] }
private def fee (i:Choir d):ℕ:=Sum.elim (fun j=>2*(j.val+2)) spinWeight i
private abbrev groom (t:ℝ): Marker B d→L[ℝ]Marker B d:= Drives.road (E:=Marker B d) (part B d) (fee d) t
private abbrev cords (t:ℝ) (x:Lugs d B): Lugs d B:=fun j=> t^(spinWeight j) • x j
 --
variable {B d}
private lemma sums_pc (x:Marker B d)(t:ℝ): groom B d t x=(engineered (t^2) x.1,cords B d t x.2):=by
   rw [groom, Drives.road_at,Fintype.sum_sum_type]; apply Prod.ext; simp only [Prod.fst_add,Prod.fst_sum]
   · rw [Parts.spread_scale]; change ((∑ i:Fin (d/2-1), t^(2*(i.val+2)) • (Pi.single i (x.1 i):Ln d))+(∑ j:UV.Multi d, t^(spinWeight j) • 0))=_; simp [pow_mul, ← Pi.single_smul] -- dependent
   simp only [Prod.snd_add,Prod.snd_sum]; change ((∑ i: Fin (d/2-1), t^(2*(i.val+2)) • 0)+(∑ j:UV.Multi d,t^(spinWeight j) • (Pi.single j (x.2 j): Lugs d B)))=cords B d t x.2; funext p; simp only [smul_zero, sum_const_zero, zero_add, Finset.sum_apply]; rw [Finset.sum_eq_single p]; · simp [cords]
   · intro i _ hi; simp [Pi.single_eq_of_ne hi.symm]
   simp
private lemma sings_pc (p:Choir d)(t:ℝ)(X: Marker B d): groom B d t (part B d p X)=t^(fee d p) • (part B d p X):=by
    cases p with
    | inl i=> rw [sums_pc]; apply Prod.ext
              · change engineered (t^2) (Pi.single i (X.1 i))=t^(2*_) • (Pi.single i (X.1 i): Ln d); funext j; by_cases h:j=i <;> simp [Pi.single_apply,engineered_at,h,pow_mul]
              change cords B d t 0=t^_ • 0; simp only [smul_zero]; funext k; change t^_ • (0:Flet B)=0; rw [smul_zero]
    | inr j=> rw [sums_pc]; apply Prod.ext; · change engineered (t^2) _=t ^_ • _; change engineered (t^2) (0 : Snap su (d/2))=t^_ • 0; funext i; simp [engineered_at]
              change cords B d t (Pi.single j (X.2 j))=t^(spinWeight j) • (Pi.single j (X.2 j): Lugs d B); funext i; by_cases h:i=j <;> simp [Pi.single_apply,h,cords]
private lemma sonic (p:Choir d) : 0 < fee d p :=by cases p <;> simp [fee,spinWeight] -- positive
private lemma sole_pc (x:Marker B d) : groom B d 1 x=x:=by
   rw [sums_pc]; apply Prod.ext; funext i; simp [engineered_at]; funext i; simp [cords]
abbrev play (H:TaperHol)(b:Cover)(F:Grid c → Lat.Fields c 6)(X: Marker B d) : Alg B :=changeVars (scoring H.T b X.2) (F (views H b d X.1))
variable (H:TaperHol) (F: Grid c→Lat.Fields c 6)
private lemma prograde (x:Lugs d B)(t:ℝ) : scoring T (c:=c) b (cords B d t x)= let s:Matrix _ _ ℂ:=flats x; let W:Matrix _ _ ℂ:= chain T b t d (c:=c)*s; show VectorD (Site c) B from W:=by
   apply flat_ext; intro i; funext j k
   unfold asks scoring; try dsimp only
   rw [Matrix.mul_apply,Matrix.mul_apply,← Equiv.sum_comp (stretch (UV.Multi d)) (fun i'=>chain T b 1 d _ i' * flats _ i' k),← Equiv.sum_comp (stretch (UV.Multi d)) (fun i'=>chain T b t d _ i' * flats _ i' k)] -- Need hint
   refine Finset.sum_congr rfl fun y _=>?_ ; cases y with | mk p v =>
   rw [scion,scion]; unfold flats; try dsimp only
   rw [Equiv.symm_apply_apply]
   by_cases hv:j=v; swap; · simp only [if_neg hv,zero_mul]
   simp only [if_pos hv, profile, cords, one_pow, one_mul,Complex.real_smul, Complex.ofReal_pow,Complex.ofReal_mul,Pi.smul_apply]; ring
lemma signed_up (X: Marker B d)(t:ℝ): play H b F (groom B d t X) = changeVars (flats X.2) (moment H b (expand _ X.1) F t):=by
   unfold play Beacon.moment; rw [sums_pc]; try dsimp only
   rw [prograde]; try dsimp only
   change changeVars (_* (show Matrix _ B ℂ from flats X.2)) _= changeVars _ (changeVars _ _); rw [change_mul]; rw [show (current H b d (expand _ X.1) t)=views H (c:=c) b d (engineered (t^2) X.1) by unfold current; rw [expand_jet,trunks]]; rfl
lemma live_play (hf:ContDiffAt ℝ d (F ∘ increment 1) 0): ContDiffAt ℝ d (play (B:=B) (d:=d) H b F) 0:=by
    let A(X:Marker B d):= views (c:=c) H b d X.1
    obtain ⟨L,hL⟩:=scoring_cl H.T b (B:=B) (d:=d) (c:=c)
    let f:=lamp H b (d:=d) (c:=c) ∘ Prod.fst (β:=Lugs d B); have he : ContDiffAt ℝ d f 0:= ((fluent H b d c).contDiffAt.of_le le_top).comp (f:=Prod.fst) _ contDiffAt_fst
    have ht : f 0=0:=at_dark H b
    have hF : ContDiffAt ℝ d (F∘A) 0:=by
       apply ((ht.symm ▸ hf).comp (f:=f) _ he).congr_of_eventuallyEq
       filter_upwards [(continuous_fst (Y:=Lugs d B) |>.tendsto (0:Marker B d)).eventually (at_east (c:=c) H b)] with X hX; exact congr_arg F hX
    apply aperture (F∘A) ((scoring H.T b (c:=c)) ∘ Prod.snd (α:=Ln d)) _ _ hF; rw [← hL]; exact L.contDiff.contDiffAt.comp _ contDiffAt_snd
set_option synthInstance.maxHeartbeats 380000 in
set_option maxHeartbeats 1400000 in
lemma exalt (hf:ContDiffAt ℝ d (F ∘ increment 1) 0)(ht:∀ (J:Labels.Jet su)(k:ℕ),k<n→ leading k (moment (d:=d) H b J F)=0)(hn:n≤d+1) (a:Fin l→ℕ) (ha:(∑ i,a i)<n)(hl:l≤d)(X:Fin l→Marker B d) (hX:∀ i, throughSlot (X i).1 (a i/2))(hB:∀ i p,a i<spinWeight p→ (X i).2 p=0): iteratedFDeriv ℝ l (play H b F) 0 X =0:=by
   apply Drives.capped (E:=Marker B d) (part B d) (fee d) _ (live_play b H F hf) hl a sonic sole_pc (fun i x t=> sings_pc ..) ha hn _ X -- h param order.inspect
   · intro i j hj; cases j with
     | inl v=> change ((Pi.single v ((X i).1 v),0):Marker B d)=0; change a i<2*(v.val+2) at hj; rw [hX i v (by omega),Pi.single_zero]; rfl
     | inr j=> change ((0,Pi.single j ((X i).2 j)):Marker B d)=0; rw [hB i j hj,Pi.single_zero]; rfl
   intro x k hk; simp_rw [signed_up]; apply leading_zero_iff.mpr
   let K:= (changeVars (flats x.2)).toLinearMap; let L:=K.restrictScalars ℝ; let J:= expand _ x.1
   have hh:ContDiffAt ℝ k (moment (d:=d) H b J F) 0:= by
       have he := Beacon.obtainsD H b F hf -- order ↑
       obtain ⟨y,hy,h⟩:=he; exact (h J).1.of_le (by exact_mod_cast Nat.le_of_lt_succ (hk.trans_le hn))
   change iteratedDeriv k (L.toContinuousLinearMap ∘ moment H b J F) 0=0; rw [Display.clm_step _ _ _ hh,leading_zero_iff.mp (ht J k hk),map_zero]
end Pipes
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Pipes.exalt
