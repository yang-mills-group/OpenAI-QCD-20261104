import YM.Poised.Permit
/-! # Prices the one common explicit UV Calibration section at all the masked
stops. Use established P.Exhibit with fold cluster estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Display Papyrus MassiveQCD.Plate QCD.Kites
variable {c : Side} {d k n m r p w : ℕ}
namespace Carte
open Beacon Next.Foundations Costs Lining Lining.Temper Ferry Merian Sieve Permit Work.G06 Work.G07
open Collage
local notation "Ψ"=>Lat.Fields c 6
local notation "Z"=> SpinPol d
variable (U:Hol su)(A: Exhibit U)
namespace Cells
variable {U A}
abbrev ReelM(h:Hol su)(A:Exhibit h)(d:ℕ):= Nearest (A.t d) 6
local notation "T" => ReelM U A d
local notation "N" => Pairs T
lemma powered (f:Land→ℂ)(hp: Lease r k m 1 f)(w:ℕ) : Lease r k m w (fun x=> f x^w):=by induction w with | zero=> simpa using (Lease.cup (r:=r) (k:=k) (p:=m) (1:ℂ))| succ w ih=> simp_rw [pow_succ]; exact ih.product hp
variable (U A)
lemma paintedD (i: PowerPair d)(H:used_bound (A.t d) r)(k m:ℕ): Lease r k m (life i.1) (fun X=> Labels.read (extraction (A.F d) X) (MvPolynomial.monomial i.1 1)):=by
    have hp (a:Labels.Key su): Lease r k m 1 (fun x=> Labels.coord (extraction (A.F d) x) a):= rarity (A.t d) U (A.F d) (Work.G05.snapCoord _ a).toLinearMap (A.sel d).panel H k m
    simp only [Labels.read, MvPolynomial.aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply, one_mul]
    unfold Finsupp.prod life; generalize i.1.support = u
    induction u using Finset.induction_on with
    | empty=> simp only [Finset.prod_empty,Finset.sum_empty]; exact Lease.cup (1:ℂ)
    | insert a s h ih=> simp_rw [prod_insert h,sum_insert h]; exact (powered _ (hp a) _).product ih
abbrev listing (p:PowerPair d)(x:Land): Dirac (ReelM U A d):= glaze (A.F d) (A.U d) (A.t d) x (gen p)
lemma spins (y:SpinPol d)(r k m:ℕ): Lease r k m 0 (fun i=> ink (A.U d) (A.t d) i y):=by
    -- Use explicit Ford polynomial = factor porch then basis terms
    obtain ⟨q,hq⟩:= Ford.sunlight (A.F d) (A.U d) (A.sel d) y; rw [← hq]; clear hq
    induction q using TensorProduct.induction_on with
    | zero=> simp_rw [map_zero]; exact Lease.cup _
    | tmul u v=> simp_rw [porch_air]; let L:= ((LinearMap.toSpanSingleton ℂ (Dirac T) v).restrictScalars ℝ).toContinuousLinearMap
                 exact (ground _ (show Work.G06.EntryPoly (A.t d) (fun i:Land=>MvPolynomial.aeval (Source.entry i) u) from ⟨u,fun _=>rfl⟩) r k m).linear L
    | add x y hx hy=> simp_rw [map_add]; exact hx.add hy
lemma copay (i: PowerPair d)(H:used_bound (A.t d) r)(k m:ℕ): Lease r k m (life i.1) (listing U A i):=by
    let P:=fun X=> Labels.read (extraction (A.F d) X) (MvPolynomial.monomial i.1 1); let L:= ((LinearMap.toSpanSingleton ℂ (Dirac T) 1).restrictScalars ℝ).toContinuousLinearMap
    let M:= fun X=>ink (A.U d) (A.t d) X (mono i.2)
    have he:listing U A i=fun x=> L (P x)*M x:=by funext v; rw [listing,gen,stencil]; unfold M; change P v • M v=(P v • (1:Dirac T))*M v; rw [smul_mul_assoc, one_mul]
    rw [he]; exact ((paintedD U A i H k m).linear L).product (spins U A _ r k m)
lemma porch_part (i:PowerPair d)(x:Land): listing U A i x∈ layer N i.2.card:=by unfold listing gen; rw [stencil]; exact Submodule.smul_mem _ _ (exterior_layer _ (Grass.homogeneous _))
lemma listing_floor (i:PowerPair d) : LocalOn (A.t d) (listing U A i) :=by
   obtain ⟨p,hp⟩:= Ford.cake (A.F d) (A.U d) (A.sel d) (gen i); have he: listing U A i= fun u=> porch (A.t d) u p:=hp.symm; rw [he]; intro V W h; dsimp only; unfold porch; rw [show Source.entry V (S:=A.t d)=Source.entry W from funext fun i=> by unfold Source.entry; rw [h _ i.1.property.1 i.1.property.2]]
lemma listedC (i:PowerPair d) : Continuous (listing U A i):=by obtain ⟨p,hp⟩:= Ford.cake (A.F d) (A.U d) (A.sel d) (gen i); exact (show _ = listing U A i from hp) ▸ porch_c (A.t d) p -- orientation not rfl
end Cells
open Cells
variable {U}
variable (S:Finset Cover)(b:Cover)
local notation "I"=>Pairs (Modes c 6)
local notation "T"=>Nearest S 6
local notation "N"=> Pairs T
def perigee (c: Side)(b:Cover) (S:Finset Cover) (v : Dirac (Nearest S 6)) : Lat.Fields c 6 := adapter (belt c S b) (belt c S b) v
-- borrow Graticule.Slide.cost/canonical. Derivatives.tWeight background
namespace Hem
variable {A}
def lip (x : T) : Modes c 6:= ((wrap c (x.1.1.val+b),x.1.2),x.2)
abbrev tongue : Dirac T→ₐ[ℂ]Ψ:= adapter (belt c S b) (belt c S b)
lemma mouthP (i:T) : tongue (c:=c) S b (psi i)= ap c (i.1.1.val+b) • psi (lip S b i):=by rw [tongue, adapt_psi]; suffices h: ∑ j:Modes c 6,(if lip S b i=j then ap c (i.1.1.val+b) else 0) • psi j= _ from h; simp [ite_smul]
lemma mouthK (i:T) : tongue (c:=c) S b (bar i)= ap c (i.1.1.val+b) • bar (lip S b i):=by rw [tongue, adapt_bar]; suffices h:∑ j:Modes c 6,(if lip S b i=j then ap c (i.1.1.val+b) else 0) • bar j= _ from h; simp [ite_smul]
lemma units_pay (i:N): ‖tongue (c:=c) S b (atom i)‖=1:=by
   rcases i with i|i
   · change ‖tongue (c:=c) S b (psi i)‖=1; rw [mouthP,norm_smul,length_pay]; simp [psi]
   change ‖tongue (c:=c) S b (bar i)‖=1; rw [mouthK,norm_smul,length_pay]; simp [bar]
open Lining Stew Cove Creek
noncomputable def pot (w:ℕ) (n: Side)(b:Cover): Support n:= halo w {wrap n b}
lemma unit_tag (i:T) (hu:used_bound S r): (lip S b i (c:=c)).1.1∈pot r c b:=by
    refine halo_spec.mpr ⟨wrap c b,mem_singleton_self _,?_⟩; unfold lip; dsimp only; rw [map_add]; exact marches S _ _ hu i.1.1.property
lemma tongue_region (i:N) (hu:used_bound S r) : tongue (c:=c) S b (atom i)∈ region (limits (pot r c b)):=by
    rcases i with i|i
    · change tongue (c:=c) S b (psi i)∈_; rw [mouthP]; exact Subalgebra.smul_mem _ (Creek.marked (Sum.inl (lip S b i (c:=c))) (Cove.limits (pot r c b)) ((mem_filter).mpr ⟨mem_univ _,unit_tag S b i hu⟩)) _
    change tongue (c:=c) S b (bar i)∈_; rw [mouthK]; exact Subalgebra.smul_mem _ (Creek.marked (Sum.inr (lip S b i (c:=c))) (Cove.limits (pot r c b)) ((mem_filter).mpr ⟨mem_univ _,unit_tag S b i hu⟩)) _
lemma ranch (x:Dirac T)(hu:used_bound S r):tongue (c:=c) S b x∈ region (limits (pot r c b)):= by
    induction x using ExteriorAlgebra.induction with
    | algebraMap s=> rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem ..
    | ι v=>rw [line_atoms]; simp only [map_sum,map_smul]; exact Subalgebra.sum_mem _ (fun _ _=> Subalgebra.smul_mem _ (tongue_region S b _ hu) _)
    | add x y hx hy=>rw [map_add]; exact Subalgebra.add_mem _ hx hy
    | mul x y hx hy=>rw [map_mul]; exact Subalgebra.mul_mem _ hx hy
lemma tongue_pay (x:Dirac T): ‖perigee c b S x‖ ≤ ‖x‖ :=by
   let T':= tongue (c:=c) S b; have he(l: List N): ‖T' (l.map atom).prod‖ ≤1:=by induction l with| nil=>simp|cons i l ih=> simp only [List.map_cons,List.prod_cons,map_mul]; exact (norm_mul_le ..).trans (by rw [units_pay,one_mul]; exact ih)
   change ‖T' x‖≤_; conv_lhs=>rw [← write x,map_sum]
   simp_rw [map_smul]; apply (norm_sum_le ..).trans; rw [Grass.norm_def x]; refine Finset.sum_le_sum fun i _=> ?_; rw [norm_smul]; apply mul_le_of_le_one_right (norm_nonneg _); obtain ⟨f,-,-,H⟩:= expression i; rw [H]; simpa only [List.map_ofFn] using he (List.ofFn f)
lemma pennyT (q:ℕ)(x : Dirac T)(hu:used_bound S r)(p:ℝ)(hp:0<p)(hv:x∈layer N n): view (wrap c b) q (perigee c b S x) p ≤ (1+(r:ℝ))^q*p^n*‖x‖:=by
   let y:= perigee c b S x; let o:=wrap c b; let u:= (1+(r:ℝ))^q; have hy:y∈layer I n:= exterior_layer _ hv; have hr:y∈ region (limits (pot r c b)):= ranch S b x hu
   have hf(s: Finset I): toll o q s p* ‖coef s y‖≤ u*p^n * ‖coef s y‖:=by
      by_cases he:coef s y=0; · simp [he]
      have hw:s⊆limits (pot r c b):=by by_contra h; exact he (ember y hr s h)
      have hk:s.card=n:= by by_contra h; exact he (Grass.spectrum hy _ h)
      have hh : s.sup (lens o) ≤ r:=Finset.sup_le fun i hi=>by obtain ⟨p,hp,hk⟩:=halo_spec.mp ((mem_filter.mp (hw hi)).2); rw [mem_singleton.mp hp, separation_comm] at hk; exact hk
      unfold toll; rw [hk]; unfold u o; gcongr -- edit
   apply (Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=> hf i)).trans; rw [← Finset.mul_sum,← Grass.norm_def y]; exact mul_le_mul_of_nonneg_left (tongue_pay S b x) (mul_nonneg (show 0≤u by unfold u; positivity) (pow_nonneg hp.le _))
end Hem
end Carte
end YM.Massive.Poised
