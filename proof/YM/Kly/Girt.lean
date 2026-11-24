import YM.Kly.Juniper
set_option autoImplicit false
set_option maxHeartbeats 610000
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis
open OS (Cross)
open Fields (pointMoment distinct)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder
open MassiveTwoEstimates Spinor Spinor.Lift
variable {F:Fields} {S:F.Kernel}{V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(R:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){X:Bases F}{M':Momentum F}(U:X.Content C M')
variable {n:ℕ}(x:Points n)(v:Fin n→F.W)
local notation "t₀"=>timeAxis
local notation "Ω"=> P.algebra
variable (A:V.VacuumOp →L[ℂ]ℂ) (X': P.algebra→⋆ₐ[ℂ]ℂ)(hX:Continuous X')
local notation "G"=> bloom P H X'
include P H Y E
variable (j D':ℕ)
lemma glory (p: EuPin):∃ W:ℝ,0<W∧∀ x:F.W,x∈ F.level D'→ ‖x‖ ≤ 1→‖F.action p x‖ ≤ W:=by
      haveI:= E.finite D'; let A:= ((F.action p).toLinearMap.comp (F.level D').subtype).toContinuousLinearMap; refine ⟨‖A‖+1,by positivity,fun x hx hz=>?_⟩; change ‖A ⟨x,hx⟩‖≤ _; exact ((A.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) hz)).trans (lt_add_one _).le
lemma ratedM (W:ℝ)(h:0<W): ∃ (k:ℕ)(B:ℝ), 0≤B ∧ ∀ (d:ℝ≥0)(p:Cluster F), Slab t₀ d p → p.length=j → (∀ x∈p,x.2 ∈ F.level D'∧‖x.2‖≤W)→∀ r:ℝ,0<r→ r≤1 → buffer t₀ r d p→ ‖P.place d p‖≤ B*r⁻¹^k :=by
     obtain ⟨k,B,hB,ht⟩:= P.rated Y j D'; let z:=(↑W:ℂ)⁻¹; have hz:z≠0:= inv_ne_zero (by exact_mod_cast h.ne'); refine ⟨k,‖z^j‖⁻¹*B, mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hB,?_⟩; intro d p hv hx hw r h₁ h₂ hp
     have hh: ‖P.place d (widen p z)‖≤ B*r⁻¹^k:=by
            apply ht _ _ (widened hv z) (by simp[widen,hx]) _ r h₁ h₂
            · refine ⟨?_,fun i hi=>?_⟩; · -- spaced
                  have hm(p:Cluster F)(x:Points p.length)(he:x=positions p):widen p z = realize (fun j=> z • tokens p j) x:=by unfold widen; nth_rw 1 [← knit p]; rw [he]; exact List.map_ofFn
                  rw [hm p (positions p) rfl]; apply (realize_spaced ..).2 hp.1
              obtain ⟨u,h,rfl⟩:= List.mem_map.mp hi; exact hp.2 u h
            intro x hx; obtain ⟨u,hu,rfl⟩:= List.mem_map.mp hx; refine ⟨Submodule.smul_mem _ _ (hw u hu).1,?_⟩; simp only [z,norm_smul,norm_inv,Complex.norm_real, Real.norm_of_nonneg h.le]; exact (inv_mul_le_iff₀ h).2 (by simpa using (hw u hu).2)
     have he:P.place d (widen p z)= (z^j) • P.place d p:=by apply V.GNS.by_bud; intro i; rw[P.reads (widened hv z), scaled_plant V hv,hx,ContinuousLinearMap.smul_apply,P.reads hv]
     rw [he,norm_smul] at hh; rw [mul_assoc]; exact (le_inv_mul_iff₀ (norm_pos_iff.mpr (pow_ne_zero _ hz))).2 hh
omit H Y E P
structure Leads (F:Fields) (i:Axis)(p:EuPin):Prop where
      crest: p.IsRotation
      axial(x:E4): Ortho.move p.coord x t₀= x i
      spots:Ortho.move p.coord (basis i)=basis t₀
      cubic(x y:E4): cubedist (Ortho.move p.coord x) (Ortho.move p.coord y)=cubedist x y
      film(x:F.W): F.action p (F.adj i x)=F.adj t₀ (F.action p x)
variable {i:Axis}{p:EuPin}(hp:Leads F i p)
include R hp
lemma rotR (x:Cluster F): rotate (reflect x i) p= reflect (rotate x p) t₀:=by
      have he(b x): Ortho.move (Signed.reflect b) x=x- (2*x b) • basis b:=by ext c; rw[Signed.mirrored]; by_cases h:c=b<;> simp [h]; ring
      simp only[rotate,reflectedPoint,←List.map_reverse,List.map_map]; congr 1; funext y; change (Ortho.move _ _, F.action p (F.adj i _))=(Ortho.move _ _,F.adj t₀ _); dsimp only; rw [he i,he t₀,hp.axial, hp.film]; change ((Ortho.motion _) _, _)=_; rw[map_sub,map_smul, show (Ortho.motion p.coord) (basis i)=_ from hp.spots]; rfl
lemma rome(x:Cluster F)(hx:Positive x i): Positive (rotate x p) t₀:=by
     refine ⟨(trans R hx.1 p).1,fun y hy=>?_⟩; obtain ⟨u,hu,rfl⟩:= List.mem_map.mp hy; change 0<Ortho.move _ _ _; rw[hp.axial]; exact hx.2 u hu
lemma loud (w:Cluster F)(d:ℝ≥0)(r:ℝ)(hv:0<r)(ht:Slab i d w)(hq: buffer i r d w): Slab t₀ d (rotate w p)∧buffer t₀ r d (rotate w p):=by
      have hx:∀ y∈ rotate w p,r≤ y.1 t₀∧ y.1 t₀≤ (d:ℝ)-r:=by
             intro y hy; obtain ⟨u,hu,rfl⟩:=List.mem_map.mp hy; change _≤ Ortho.move p.coord _ t₀ ∧ Ortho.move p.coord _ t₀≤ _; rw[hp.axial]; exact hq.2 _ hu
      refine ⟨⟨ht.1,rome R hp w ht.2.1,fun i hi=>(hx i hi).2.trans_lt (sub_lt_self _ hv)⟩,?_,hx⟩
      have he: rotate w p= realize (F.action p ∘ tokens w) (Points.move p.coord (positions w)):=by
                unfold rotate; nth_rw 1[←knit w]; rw[realize,List.map_ofFn]; rfl
      rw[he]; refine (realize_spaced ..).2 (fun x y h=>?_); exact (hp.cubic (positions w x) (positions w y)).symm ▸ hq.1 x y h -- rewrite
lemma bronze (w z:Cluster F)(d:ℝ≥0): rotate (linked i d w z) p= linked t₀ d (rotate w p) (rotate z p):=by
      rw [show linked i d _ _= w++carry z ((d:ℝ) • _) from rfl, rotated]; have ht: Ortho.move p.coord ((d:ℝ) • basis i)= _:= (Ortho.motion p.coord).map_smul _ _; rw [ht, show (Ortho.motion p.coord) (basis i)= _ from hp.spots]; rfl
variable (ha:∀ x:F.W,F.adj t₀ (F.parity x)=F.parity (F.adj t₀ x))
omit hp
include ha R H P E U Y
lemma hail (p:EuPin)(b:Cluster F)(hb:distinct b)(hp:p.IsRotation): pointMoment (G) (rotate b p)=pointMoment (G) b:=by rw [bless P H X' _ (trans R hb p).1, bless P H X' _ hb]; exact congr_arg X' (honorP P H Y R E U ha (⟨b,hb⟩) p hp)
include hp
lemma vibes :∀ (n:ℕ)(l:Fin n→Cluster F)(u:Fin n→ℂ),(∀ j, Positive (l j) i)→ Fields.gram G i l u= Fields.gram G t₀ (fun j=>rotate (l j) p) u:=by
      intro n l u he; unfold Fields.gram; apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; change _=_*pointMoment G (reflect _ _ ++ _) * _; rw[←rotR R hp,← show rotate _ _= _ from (?_ : rotate (reflect (l x) i++l y) p=rotate (reflect (l x) i) p++rotate (l y) p), hail P H Y R E U X' ha p _ (twoSides (he x) (he y)) hp.crest]; unfold rotate; rw [List.map_append]
lemma sober : Fields.Slabs G i:=by
      constructor; intro j D; obtain ⟨W,h,hW⟩:= glory P H Y E D p; obtain ⟨m,B,hB,Hx⟩:= ratedM P H Y E j D W h; refine ⟨m,B,hB,?_⟩; intro d r hd hr ht x h₁ hx hS n l hl u; let d':ℝ≥0:=⟨d,hd.le⟩; have he:Slab i d' x:= ⟨hd,⟨spaced_conf hr hx.1, fun y hy=>hr.trans_le (hx.2 y hy).1⟩, fun y hy=> (hx.2 y hy).2.trans_lt (sub_lt_self _ hr)⟩; obtain ⟨h₂,hv⟩:= loud R hp x d' r hr he hx
      let v(j:Fin n):Future F t₀:= ⟨_,rome R hp (l j) (hl j)⟩; let L:= B*r⁻¹^m; have hb:‖P.place d' (rotate x p)‖ ≤L:=by
           apply Hx _ _ h₂ (by simp[rotate,h₁]) _ r hr ht hv; intro t ht; obtain ⟨y,hy,rfl⟩:= List.mem_map.mp ht; exact ⟨E.lift _ (hS y hy).1 p, hW y.2 (hS y hy).1 (hS y hy).2⟩
      change Fields.gram G i (fun j=> linked i d' x (l j)) u≤ _; rw [vibes P H Y R E U X' hp ha _ _ u (fun j=>appendsFuture he (hl j)),vibes P H Y R E U X' hp ha _ l u hl]; simp_rw [bronze R hp]; exact payQ P H Y E X' v u d' _ h₂ L (mul_nonneg hB (pow_nonneg (inv_nonneg.mpr hr.le) _)) hb
lemma incense :∀ (n:ℕ)(l:Fin n→ Cluster F), (∀ j,Positive (l j) i) →∀ u: Fin n→ℂ,0≤ Fields.gram G i l u:=by intro n l h u; rw [vibes P H Y R E U X' hp ha _ l _ h]; exact realPr P H Y E X' (fun i=>⟨_,rome R hp (l i) (h i)⟩) u
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.incense
#print axioms YM.Massive.Bridge.Kly.sober
