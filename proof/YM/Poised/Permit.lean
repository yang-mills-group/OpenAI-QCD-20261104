import YM.Poised.Merian
/-! # Common section canonical valuations through arbitrarily large stencil order,
    threshold gain from curvature-cost Health, even for unread fields outside. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Display Papyrus MassiveQCD.Plate QCD.Kites
variable {c : Side} {d k n m r p w : ℕ}
namespace Permit
open Beacon Next.Foundations Costs Lining Lining.Temper Ferry Merian Sieve Work.G06 Work.G07
open Collage
local notation "Ψ"=>Lat.Fields c 6
local notation "Z"=> SpinPol d
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
def Lease (r k p w : ℕ)(f:CoverConfig su→E) := ∃ C :ℝ,0≤C ∧ ∀ (B:BudgetPoint)(n:Side)(o:Site n),2*(r+1)<n.val → B.power=p → LeftBound k (B.dirBound o) (Healthy B.threshold (halo (r+1) {o})) 1 (C*B.threshold^w) (f ∘ expandAt o)
namespace Lease
variable {f g : CoverConfig su→E}
lemma add (h:Lease r k p w f)(hp:Lease r k p w g): Lease r k p w (fun i=>f i+g i):=by
   obtain ⟨C,ht,hX⟩:=h; obtain ⟨D,hδ,hψ⟩:=hp; refine ⟨C+D,add_nonneg ht hδ,fun b c o he hP=>?_⟩; rw [add_mul]; exact (hX b c o he hP).add (hψ b c o he hP)
lemma linear (h:Lease r k p w f)(L:E→L[ℝ]F): Lease r k p w (L∘f):=by
   obtain ⟨C,ht,hX⟩:=h; refine ⟨‖L‖*C,mul_nonneg (norm_nonneg _) ht,fun b c o he hP=>?_⟩; rw [mul_assoc]; exact (hX b c o he hP).postcomp L
lemma product {R:Type*}[NormedRing R][NormedAlgebra ℝ R]{f g:CoverConfig su→R} (h:Lease r k p w f)(hp:Lease r k p d g): Lease r k p (w+d) (fun i=>f i*g i):=by
   obtain ⟨C,ht,hX⟩:=h; obtain ⟨D,hδ,hψ⟩:=hp; refine ⟨2^k*C*D,by positivity,fun b c o he hP=>?_⟩; have hb:= (hX b c o he hP).mul (hψ b c o he hP) zero_le_one; convert hb using 1; first|ring|rfl
   rfl
lemma cup (e:E): Lease r k p 0 (fun _=> e):=by refine ⟨‖e‖,norm_nonneg _,fun b c o he hP=>?_⟩; rw [pow_zero,mul_one]; exact LeftBound.const (by linarith) e
lemma nil : Lease r k p w (fun _ : CoverConfig su => (0:E)):= by refine ⟨0,rfl.le,fun b c o he hP=>?_⟩; rw [zero_mul, ← norm_zero (E:=E)]; exact LeftBound.const zero_le_one _
lemma wealth {ι:Type*}(x:Finset ι)(g:ι→Land→E)(hg:∀ i∈x,Lease r k p w (g i)) : Lease r k p w (fun u=>∑ i∈x,g i u):=by
    induction x using Finset.induction_on with
    | empty=> simpa only [sum_empty] using (Lease.nil (E:=E))
    | insert i s h hx=> simp_rw [sum_insert h]; exact (hg i (mem_insert_self ..)).add (hx fun j hj=>hg j (mem_insert_of_mem hj))
lemma wider {S:Finset Cover}(h:Work.G07.Rate k p S w 1 f)(H:∀ (n:Side)(o:Site n), S.image (fun x=> wrap n x+o)⊆halo (r+1) {o}): Lease r k p w f:=by
    obtain ⟨C,hc,hf⟩:=h; refine ⟨C,hc,fun b c o _ hB=>?_⟩; have he:= hf b hB c o; refine ⟨he.smooth, he.nonneg, fun l hl hd U hx=> ?_⟩; simp only [one_pow, mul_one]; exact (he.bound l hl hd U (hx.mono_left (H _ _))).trans (mul_le_of_le_one_right he.nonneg (pow_le_one₀ (pow_nonneg b.threshold_pos.le _) (pow_le_one₀ b.threshold_pos.le b.threshold_le))) -- count args
end Lease
section Revenue
variable (S:Finset Cover)(i : Source.Index su S) {f : Land→ℂ}
def used_bound (S:Finset Cover)(r:ℕ):= ∀ v∈S,∀ i:Axis,(v i).natAbs ≤ r
lemma eventual (S:Finset Cover):∀ᶠ r:ℕ in atTop, used_bound S r:= (eventually_all_finset S).mpr (fun i _=> eventually_all.mpr (fun a => eventually_ge_atTop _))
lemma marches (o:Site c)(x:Cover)(he:used_bound S r)(hx:x∈S): separation o (wrap c x+o) ≤ r:=by
    rw [separation_comm,separation,add_sub_cancel_right]; apply Finset.sup_le; intro i _; exact (Corona.lap ..).trans (he x hx i)
lemma halos (B:ℕ)(h: r≤ B) (o:Site c)(he:used_bound S r): S.image (fun x=>wrap c x+o)⊆halo B {o}:=by
   intro i hi; obtain ⟨x,hx,rfl⟩:= mem_image.mp hi; exact halo_spec.mpr ⟨_,mem_singleton_self _,(marches S o x he hx).trans h⟩
private theorem array (h:EntryPoly S f)(k p:ℕ)(T:Finset Cover):Work.G07.Rate k p T 0 1 f :=by
   obtain ⟨x,h⟩:=h; rw [← funext h]; clear h
   induction x using MvPolynomial.induction_on with
   | C a=> simpa only [MvPolynomial.aeval_C,Algebra.algebraMap_self,RingHom.id_apply] using (Work.G07.Rate.const (G:=su) a)
   | add p q hp hq=> simp_rw [_root_.map_add]; exact hp.add hq
   | mul_X p i hp=>
      simp_rw [_root_.map_mul,MvPolynomial.aeval_X]; apply hp.mul (j:=0)
      let L : su.Mat →L[ℝ] ℂ:= LinearMap.toContinuousLinearMap { toFun:=fun x=>x i.2.1 i.2.2.1,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}; unfold Source.entry; dsimp only; split; exact Work.G07.Rate.postcomp (rate_link i.1.val) ((starL' ℝ : ℂ≃L[ℝ]ℂ).toContinuousLinearMap.comp L)
      exact Work.G07.Rate.postcomp (rate_link i.1.val) L
lemma ground (h:EntryPoly S f)(r k p:ℕ): Lease r k p 0 f:= Lease.wider (array S h k p ∅) (by simp)
-- amount small from ALL inspected healthy faces; no high branch if off. Worth as primitive.
lemma fresh (h:EntryPoly S f) : ∃ C:ℝ,0≤ C∧ ∀ (x : Land)(δ:ℝ),0 ≤ δ→ (∀ i: Source.Index su S, ‖Source.entry x i- Source.entry 1 i‖ ≤ δ) → ‖f x-f 1‖ ≤ C*δ:=by
    obtain ⟨p,hp⟩:= h; simp_rw [← hp]; clear hp
    induction p using MvPolynomial.induction_on with
    | C a=> refine ⟨0,le_rfl,?_⟩; simp
    | add p q hp hq=>
       obtain ⟨u,hU,hu⟩:=hp; obtain ⟨v,hV,hv⟩:=hq; refine ⟨u+v,add_nonneg hU hV,fun x δ hd he=>?_⟩; simp_rw [_root_.map_add]; rw [add_sub_add_comm,add_mul]; exact (norm_add_le ..).trans (add_le_add (hu x δ hd he) (hv x δ hd he))
    | mul_X p i hp=>
       obtain ⟨u,hU,hu⟩:= hp; let g(x:Land):=Source.entry x i
       obtain ⟨C,hv⟩:= isCompact_univ.bddAbove_image (f:=fun x:Land=> ‖Source.entry x i‖) (by unfold Source.entry; dsimp only; split <;> fun_prop)
       let a:= MvPolynomial.aeval (Source.entry (1: Land)) p; have hC : 0≤ C:= (norm_nonneg _).trans (hv (mem_image_of_mem _ (Set.mem_univ (1:Land))))
       refine ⟨u*C+‖a‖,add_nonneg (mul_nonneg hU hC) (norm_nonneg _),fun x δ hd he=> ?_⟩; rw [_root_.map_mul,MvPolynomial.aeval_X,_root_.map_mul,MvPolynomial.aeval_X]; let b:=MvPolynomial.aeval (Source.entry x) p; rw [show b* g x-a*g 1= (b-a)*g x+a*(g x-g 1) from (by ring)]; apply (norm_add_le ..).trans; rw [norm_mul,norm_mul]; exact (add_le_add (mul_le_mul (hu x δ hd he) (hv (Set.mem_image_of_mem _ (Set.mem_univ x))) (norm_nonneg _) (mul_nonneg hU hd)) (mul_le_mul_of_nonneg_left (he i) (norm_nonneg _))).trans_eq (by ring)
-- F.F norm transform at identity based.V prove `NormSite`
private lemma entry_chord (x:Land)(y : Source.Index su S) : ‖Source.entry x y-Source.entry (1:Land) y‖ ≤ su.chord (x y.1.val)*Real.sqrt su.repDim:=by
    have he : ‖su.mat (x y.1.val) y.2.1 y.2.2.1-(1:su.Mat) y.2.1 y.2.2.1‖ ≤ ‖su.mat (x y.1.val)-(1:su.Mat)‖ := Fork.frob_entry (su.mat (x y.1.val)-1) y.2.1 y.2.2.1
    rw [Gauge.chord,div_mul_cancel₀ _ (show Real.sqrt (su.repDim:ℝ)≠0 from su.colorScale_pos.ne')]; unfold Source.entry; dsimp only [Pi.one_apply]; rw [su.mat_one]; split; swap; exact he
    rw [← star_sub,norm_star]; exact he
lemma clearMono {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V]{f:Land→V}(h:Paper.Plane S f) :∃ C:ℝ,0≤ C∧∀(x:Land)(δ:ℝ),0≤δ→ (∀ i: Source.Index su S, su.chord (x i.1.val) ≤ δ)→ ‖f x-f 1‖ ≤ C*δ:=by
    let p (L:V→ₗ[ℝ]ℝ): V→L[ℝ]ℝ:=L.toContinuousLinearMap
    choose C hC hP using fun i:V →ₗ[ℝ] ℝ=> fresh S (h (Complex.ofRealLI.toLinearMap.comp i))
    have he(x:V)(he:∀ i,p i x=0) : x=0:=by apply (Module.finBasis ℝ V).repr.injective; ext i; rw [map_zero]; exact he ((Module.finBasis ℝ V).coord i)
    obtain ⟨A,hA,ha⟩:=budget_probes p he C hC
    let r':=Real.sqrt su.repDim; refine ⟨A*r',mul_nonneg hA.le (Real.sqrt_nonneg _),fun x δ hd h=>?_⟩; rw [mul_assoc]; refine ha _ (mul_nonneg (Real.sqrt_nonneg _) hd) _ fun i=>?_; have hi:=hP i x (r'*δ) (mul_nonneg (Real.sqrt_nonneg _) hd) (fun j=> (entry_chord S x j).trans ((mul_le_mul_of_nonneg_right (h j) (Real.sqrt_nonneg _)).trans_eq (mul_comm ..))); change ‖(↑(i (f x)):ℂ)- ↑(i (f 1))‖ ≤ _ at hi; rw [← Complex.ofReal_sub, Complex.norm_real,←map_sub] at hi; exact hi
variable (U:Hol su)
abbrev horn (r:ℕ) : ℝ :=16*(2*((r+1:ℕ):ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ)
private lemma Taylor_paint (u:su.El)(i:ℕ)(p:Labels.Taylor su i): ‖Labels.Taylor.paint u p‖=‖p‖:=by
   -- adjoint isometry.
   suffices h:∀ (u:su.El)(p:Labels.Taylor su i),‖Labels.Taylor.paint u p‖ ≤ ‖p‖ by
      apply le_antisymm (h u p); have hh:= h u⁻¹ (Labels.Taylor.paint u p); rw [show Labels.Taylor.paint u⁻¹ _=p from ?_] at hh; exact hh
      apply Labels.Taylor.value_ext; funext i j; rw [Labels.Taylor.paint_value,Labels.Taylor.paint_value,← su.adjoint_mul, inv_mul_cancel,su.adjoint_one]
   intro u p; change ‖(Labels.Taylor.paint u p).val‖ ≤ ‖p.val‖; apply (pi_norm_le_iff_of_nonneg (norm_nonneg (p.val))).2; intro j
   apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _); intro v
   change ‖su.adjoint u (p.val j v)‖ ≤ _; rw [su.norm_adjoint]; exact ((p.val j).le_opNorm _).trans (mul_le_mul_of_nonneg_right (norm_le_pi_norm p.val j) (prod_nonneg fun _ _=> norm_nonneg _))
private lemma tollS (u:su.El)(f: Snap su d): ‖Scan.tinted u d f‖=‖f‖:=by
    classical
    have hh(y: Snap su d)(v:ℝ)(hv:0≤v): ‖y‖≤v ↔ ∀ i,‖y i‖≤v:= pi_norm_le_iff_of_nonneg hv
    apply le_antisymm; apply (hh _ _ (norm_nonneg _)).mpr; intro i; rw [show ‖Scan.tinted u d f i‖=‖f i‖ from Taylor_paint ..]; exact norm_le_pi_norm f i
    apply (hh _ _ (norm_nonneg _)).mpr; intro i; rw [← show ‖Scan.tinted u d f i‖=‖f i‖ from Taylor_paint ..]; exact norm_le_pi_norm _ _
private lemma vacant {h m:ℕ}(A:Flag U h m): A.F 1=0:=by
   have hx:= A.lens.here; rw [show Scan.trunkJ m U 0=1 from funext fun i=> (Work.G02.linkGerm U m i).2.1] at hx; exact hx
lemma harpie {w j : ℕ}(A:Flag U w j)(h:Paper.Plane S A.F)(he:used_bound S r): ∃ C:ℝ,0≤C ∧ ∀ (B:BudgetPoint)(n:Side)(o:Site n),2*(r+1)<n.val→ ∀ x:Grid n, Healthy B.threshold (halo (r+1) {o}) x → ‖A.F (expandAt o x)‖ ≤ C*B.threshold:=by
    obtain ⟨C,hC,ha⟩:= clearMono S h
    have hX:0≤horn r:=by unfold horn; positivity
    refine ⟨C*horn r,mul_nonneg hC hX, fun B n o hN x hu =>?_⟩
    obtain ⟨g,hg⟩:= Work.E08.axial_patch o x r (r+1) le_rfl hN B.threshold B.threshold_pos.le (Fork.station x o _ hu)
    have hp:= ha (expandAt o (Lattice.gauge g x)) (horn r*B.threshold) (mul_nonneg hX B.threshold_pos.le) fun i=> hg (wrap n i.1.val.1+o,i.1.val.2) (marches S o _ he i.1.property.1)
    rw [vacant U A, sub_zero,expandAt_gauge] at hp
    have hh(t : Cover→su.El) : ‖A.F (Lattice.gauge t (expandAt o x))‖ = ‖A.F (expandAt o x)‖:=by rw [A.color,tollS]
    rw [hh] at hp; rwa [mul_assoc]
private lemma lmBound {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X](L:X→ₗ[ℝ]ℂ) : ∃ C:ℝ,0≤C ∧ ∀ x,‖L x‖ ≤ C*‖x‖:= ⟨_,norm_nonneg L.toContinuousLinearMap,fun x=>L.toContinuousLinearMap.le_opNorm x⟩
set_option synthInstance.maxHeartbeats 60000 in
set_option maxHeartbeats 600000 in
lemma rarity {j h:ℕ}(A:Flag U h j) (p: Snap su j→ₗ[ℝ]ℂ)(he: Paper.Plane S A.F) (hX :used_bound S r) (k m:ℕ) : Lease r k m 1 (fun x=> p (A.F x)):=by
   obtain ⟨C,hC,H⟩:= harpie S U A he hX
   obtain ⟨W,hW,h⟩:= array S (he p) k m ∅
   obtain ⟨D,hD,hp⟩:=@lmBound (Snap su j) inferInstance inferInstance inferInstance p
   refine ⟨D*C+W,add_nonneg (mul_nonneg hD hC) hW,fun b c o hn hv=>?_⟩; have ht:= h b hv c o; simp only [pow_zero,pow_one,mul_one,_root_.map_zero,Finset.image_empty] at * -- may alter
   refine ⟨ht.smooth, mul_nonneg (add_nonneg (mul_nonneg hD hC) hW) b.threshold_pos.le,fun l hl hd x hx=>?_⟩
   rw [one_pow,mul_one,add_mul]
   cases l
   · apply ((hp (A.F (expandAt o x))).trans (mul_le_mul_of_nonneg_left (H b c o hn x hx) hD)).trans; rw [← mul_assoc]; exact le_add_of_nonneg_right (mul_nonneg hW b.threshold_pos.le)
   · apply (ht.bound _ hl hd x (by simp [Healthy])).trans; apply le_trans _ (le_add_of_nonneg_left (mul_nonneg (mul_nonneg hD hC) b.threshold_pos.le)); apply mul_le_mul_of_nonneg_left _ hW; exact (pow_le_pow_of_le_one b.threshold_pos.le b.threshold_le (by simp : 1≤ List.length _)).trans (pow_one ..).le
end Revenue
end Permit
end YM.Massive.Poised
