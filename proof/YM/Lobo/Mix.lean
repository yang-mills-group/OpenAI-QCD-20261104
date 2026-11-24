import YM.Lobo.Shrike
set_option maxHeartbeats 620000
set_option autoImplicit false
noncomputable section
namespace YM.Lobo
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Massive.Oriole UV.Free Iceberg
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open Finset
open scoped YM.Massive.Poised.Plans.Stamp
variable (f:Flavor 6)(k i j:Tri)(w:Bool)
noncomputable def hunt (f:Flavor 6)(i j:Tri): Label 10 := pulseT f false i (lieu j)
noncomputable def rente (f:Flavor 6)(i:Tri): Label 10:= pulseT f true i timeAxis
set_option quotPrecheck false
local notation "Cz" b:arg => Cane (pathW k) (Omega k) (treks k) b 10
local notation "W" => hunt f
local notation "V" => rente f
local notation "Wx"=> fun (i j:Tri)=> projection (hunt f i j)
lemma scout(u:IceT) : Cane (pathW k) (Omega k) (treks k) u 10 (hunt f i j)= (if u=none then drive k (fun i=>hunt f i j) i else 0)+(if u=some f then drive k (hunt f i) j else 0):=by
    have h(s:ℝ):putH (sectorP u (pathW k s)) 10 (W i j)= wing k (rho u none s) (fun x=>wing k (rho u (some f) s) (W x) j) i:=wagonB _ _ f i j k (rho u none s) false (coreT k u none s) _ (coreT k u (some f) s)
    have he:= tCane (pathW k) _ (treks k) u (W i j); simp_rw [h] at he
    rcases u with _|x
    · rw [if_pos rfl,if_neg (by intro h; cases h), add_zero]; apply he.unique _; simp_rw [show ∀ t, rho none none t=t from fun t=> by rw [rho,if_pos rfl],show ∀ t,rho none (some f) t= 0 from fun t=> by rw [rho,if_neg (by intro h; cases h)], fun t:Tri=> w_zero k j (W t)]; exact wingD k i (fun i=>W i j)
    rw [if_neg (by intro h; cases h),zero_add]; split <;> rename_i hT
    · have hm: x=f:= Option.some.inj hT; subst x; refine he.unique ?_; simp_rw[show ∀ t,rho (some f) none t=0 from (fun t=>by rw [rho,if_neg (by intro h; cases h)]),w_zero]; simp only[rho,↓reduceIte]; exact wingD k j (W i)
    refine he.unique ?_; simp_rw [show ∀ t,rho (some x) none t=0 from fun t=>by rw [rho,if_neg (by intro h; cases h)], w_zero, show ∀ t, rho (some x) (some f) t=0 from fun t=>by rw [rho,if_neg hT],w_zero]; exact hasDerivAt_const ..
lemma tincture (p:RawSym) : p.pin 10 (SpinQ k) (hunt f i j)=(charI k i:ℂ) • ((charI k j:ℂ) • hunt f (roof k i) (roof k j)):=by
    let P:= SpinQ k; have ht:P.coord=Thr k quarterR:= cusP k none P (fL k)
    rw [freeK]; unfold hunt; rw[wagonB _ _ _ _ _ k quarterR false ht quarterR ht, wing_Q]; simp_rw[wing_Q]
lemma cumin(p:RawSym) : p.pin 10 (SpinQ k) (rente f i)=(charI k i:ℂ) • rente f (roof k i):=by
    let P:=SpinQ k; have ht:P.coord=Thr k quarterR:=cusP k none P (fL _); rw [freeK]; unfold rente; rw[wagonC _ _ _ _ k quarterR true ht quarterR ht, wing_Q]
lemma ruin (u:IceT) : Cane (pathW k) (Omega k) (treks k) u 10 (rente f i) = if u=none then drive k (rente f) i else 0:=by
    have h(t:ℝ):putH (sectorP u (pathW k t)) _ (V i)=wing k (rho u none t) V i:=wagonC _ _ _ _ k _ true (coreT k u none t) _ (coreT k u (some f) t)
    have he:= tCane (pathW k) _ (treks k) u (V i); simp_rw [h] at he
    split <;> rename_i hz; · subst u; apply he.unique _; simp only[rho,↓reduceIte]; exact wingD ..
    apply he.unique _; simp only[rho,hz,↓reduceIte,w_zero]; exact hasDerivAt_const ..
variable (p:RawSym)(s:Hail.RightAuth p)(z:IceT→ℝ)
include s
lemma driverF (v:Tri→ Label 10) : projection (drive k v i)=drive k (fun j=> projection (v j)) i:=by unfold drive; simp only [map_sum,map_smul]
lemma truss : omegaQ k z 10 (projection (W i j)) = (z none:ℂ) • drive k (fun i=> projection (W i j)) i+ (z (some f):ℂ) • drive k ((Wx) i) j:=by
     unfold omegaQ reachΩ; simp_rw [LinearMap.sum_apply,LinearMap.smul_apply, fun u:IceT=>joins (pathW k) _ (treks k) u p s (W i j),scout f k i j,map_add, smul_add, Finset.sum_add_distrib]; refine congr_arg₂ (·+·) ?_ ?_
     · rw [sum_eq_single (none:IceT)]; rw [if_pos rfl,driverF k i p s]; -- order
       intro u _ h; rw [if_neg h,map_zero,smul_zero]
       simp
     rw [sum_eq_single (some f)]; rw [if_pos rfl,driverF k j p s]
     intro u _ h; rw[if_neg h,map_zero,smul_zero]
     simp
end YM.Lobo
#print axioms YM.Lobo.truss
#print axioms YM.Lobo.tincture
