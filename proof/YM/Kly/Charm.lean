import YM.Kly.Trim
set_option maxHeartbeats 520000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis MeasureTheory Measure UV UV.Free
open OS (Cross)
open Fields (pointMoment distinct gram)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder Matrix
variable {F:Fields} {S:F.Kernel} {V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(R:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){B:Bases F}{M':Momentum F}(U:B.Content C M')
variable (x:F.W)(w:P.algebra→⋆ₐ[ℂ]ℂ)(hx:Continuous w)
local notation "Sα"=>bloom P H w
local notation "t₀"=>timeAxis
variable (T: FlavorTorus→* (V.H≃ₗᵢ[ℂ] V.H))(hT:∀ p:FlavorTorus,∀ v,T p (V.GNS.plant v)=V.GNS.plant (boat p v))
local notation "Θ"=> P.algebra
variable (p:FlavorTorus)
include hT
local notation "J"=>hartK T hT
noncomputable def twin: Θ→⋆ₐ[ℂ]Θ:=
      { toFun:=fun x => ⟨_, grows P T hT p x⟩,map_mul':=fun x y=> Subtype.ext (map_mul (sky (J p)) x.val y.val), map_one':=Subtype.ext (map_one (sky _)), map_add':=fun x y=>Subtype.ext (map_add (sky _) x.val y.val), map_zero':=Subtype.ext (map_zero (sky _)), map_star':=fun x=>Subtype.ext (map_star (sky _) x.val), commutes':=fun r=> Subtype.ext ((sky _).commutes r) }
local notation "Tp"=> twin P T hT
variable (u:Θ)
@[simp]lemma town (u:P.algebra) : Tp 1 u=u:=by
      apply Subtype.ext; ext1 x; change sky (J _) u.val x= u.val x; rw [sick, inv_one, map_one]; rfl
lemma twine(u:P.algebra)(y:FlavorTorus):Tp (p*y) u=Tp p (Tp y u):=by
      apply Subtype.ext; ext1 x; change sky (J _) _ _=sky (J p) (sky (J y) u.val) x; rw [sick,sick,sick,mul_inv_rev,map_mul,map_mul]; rfl
include H
lemma mound (u:Pack F): M₀ P (bank p u)=Tp p (M₀ P u):=by
      obtain ⟨s,d,hs⟩:=Spread.place_exists u.property; let v:= bank p u; have he(j:Cluster F):carry (jug p j) s=jug p (carry j s):=by unfold carry jug; simp only[List.map_map]; rfl
      have hv:Slab t₀ d (carry v.val s):= he u.val ▸ sailsF p _ _ hs; unfold M₀; rw [overline P H _ u.property s hs,overline P H _ v.property s hv]; apply Subtype.ext; change P.atom (carry (jug p _) _) _=sky (J p) (P.atom (carry u.val s) d); rw [stain P T hT p (carry u.val s) _ hs,he] -- placeholders
omit H
lemma pear (x:V.VacuumOp) :‖sky (J p) x‖ ≤ ‖x‖ :=by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (E:=V.VacuumOp) x) ?_; intro v; rw [sick,LinearIsometryEquiv.norm_map]; exact (ContinuousLinearMap.le_opNorm x ((J p⁻¹) v)).trans_eq (by rw[LinearIsometryEquiv.norm_map])
lemma pyram (x y: V.VacuumOp): dist (sky (J p) x) (sky (J p) y) ≤ dist x y:=by rw[dist_eq_norm (sky (J p) x) (sky (J p) y),dist_eq_norm x y, ←map_sub]; exact pear T hT p _ --dist_eq_norm,←map_sub,dist_eq_norm]; exact pear T hT p _
omit hT
lemma capMulti {n:ℕ}{V Z:Type}[NormedAddCommGroup V][NormedAddCommGroup Z][NormedSpace ℂ V][NormedSpace ℂ Z][FiniteDimensional ℂ V](A:MultilinearMap ℂ (fun _ : Fin n=>V) Z):Continuous A:=by
      let B:= Module.finBasis ℂ V; have he(v:Fin n→V): A v=∑ i: Fin n→Fin (Module.finrank ℂ V),(∏ j,B.coord (i j) (v j)) • A (fun j=> B (i j)):=by
            have ht(j:Fin n): v j= ∑ i,B.coord i (v j) • B i:= (B.sum_repr _).symm
            conv_lhs=> rw [funext ht]
            rw[MultilinearMap.map_sum]; exact Finset.sum_congr rfl fun i _=> A.map_smul_univ ..
      rw [funext he]; exact continuous_finsetSum _ (fun j _=> (continuous_finsetProd _ (fun i _=> ((B.coord _).continuous_of_finiteDimensional.comp (continuous_apply i)))).smul continuous_const)
include hT
include E H Y
lemma posture (v: Pack F) :Continuous (fun p:FlavorTorus=> sky (J p) (M₀ P v).val):=by
      let x:= positions v.val; let n:=v.val.length; have hx:x∈conf _:= v.property; let u:= tokens v.val; have ht(p): M₀ P (bank p v)=M P (realize (F.flavor p ∘ u) x) ((realized ..).2 hx):=by
           change M P (jug p _) _= _; congr 1; unfold jug; nth_rw 1[← knit v.val]; rw[realize,List.map_ofFn]; rfl -- simpler
      obtain ⟨d,g,hg⟩:= Rotate.cover_cap E u; haveI:= E.finite d; have hv(w:F.W)(hw:w∈F.level d)(b:FlavorTorus): F.flavor b w∈ F.level d:=by
            rw[← E.identification d none] at * -- intros
            obtain ⟨t,rfl⟩:= hw; rw [E.flavor]; exact LinearMap.mem_range_self _ _
      let A(i:Fin n)(b:FlavorTorus): F.level d:= ⟨_,hv (g i).val (g i).property b⟩
      have hs(p:FlavorTorus): F.flavor p ∘ u= fun i:Fin n=> (A i p).val:=by rw[hg]; rfl
      let X : MultilinearMap ℂ (fun _ : Fin n=> ↥(F.level d)) V.VacuumOp:= P.algebra.subtype.toAlgHom.toLinearMap.compMultilinearMap ((meter P H _ x).compLinearMap (fun _=> (F.level d).subtype)); have he(p:FlavorTorus): sky (J p) (M₀ P v).val=X (fun i=>A i p):=by rw [show sky (J p) _=(M₀ P (bank p v)).val from congr_arg Subtype.val (mound P H T hT p v).symm]; unfold X; rw [mAt P H x hx]; exact congr_arg Subtype.val (ht p) |>.trans (by simp_rw[hs]; rfl)
      let b (i:Fin n):= Module.finBasis ℂ (F.level d);
      have hc (i:Fin n):Continuous (fun p=>A i p):=(E.flavorActs (g i).val).subtype_mk _; -- want X expansion all, supports La. use new lemma.
      rw [funext he]; refine (show Continuous X from ?_).comp (continuous_pi hc)
      exact capMulti (Z:=V.VacuumOp) X
lemma terrain (x:V.VacuumOp)(h:x∈Θ): Continuous fun p:FlavorTorus=> sky (J p) x:=by
      have ht (x:V.VacuumOp)(hx:x∈StarAlgebra.adjoin ℂ P.generators) : Continuous fun p:FlavorTorus=> sky (J p) x:=by
             induction hx using StarAlgebra.adjoin_induction with
             | mem x hx=>
                 obtain ⟨u,d,ht,rfl⟩:=hx; have h:= posture P H Y E T hT (⟨_,ht.2.1.1⟩); unfold M₀ at h; -- fix
                 change Continuous (fun p=>sky (J p) (M P u ht.2.1.1).val) at h; rw [spots P H ht] at h; exact h
             | add x y hx hy h1 h2=> simp only [map_add]; fun_prop
             | algebraMap r=> simp_rw [fun p:FlavorTorus=> show sky (J p) (algebraMap ℂ V.VacuumOp r)= _ from (sky (J p)).commutes r]; exact continuous_const
             | mul x y hx hy h1 h2=> simp only[map_mul]; fun_prop
             | star x hx h=> simp only [map_star]; fun_prop
      apply continuous_iff_continuousAt.mpr; intro i
      apply Metric.tendsto_nhds.mpr; intro ε he; obtain ⟨y,(hy:y∈ (StarAlgebra.adjoin ℂ P.generators)),hY⟩:= (Metric.mem_closure_iff (α:=V.VacuumOp) (a:=x)).mp (show x ∈ closure (StarAlgebra.adjoin ℂ P.generators:Set V.VacuumOp) from h) (ε/3) (by linarith) -- inequality direction
      filter_upwards[Metric.tendsto_nhds.mp ((ht y hy).continuousAt (x:=i)) (ε/3) (by linarith)] with u h; change dist (sky (J u) x) (sky (J i) x)< _; apply lt_of_le_of_lt (dist_triangle _ (sky (J u) y) _); apply lt_of_le_of_lt (add_le_add (pyram T hT ..) (dist_triangle _ (sky (J i) y) _)); have hp:= pyram T hT i y x; rw [dist_comm y x] at hp; linarith
lemma slopes(x:Θ): Continuous fun p:FlavorTorus=> twin P T hT p x:= (terrain P H Y E T hT _ x.property).subtype_mk _
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.slopes
#print axioms YM.Massive.Bridge.Kly.town
#print axioms YM.Massive.Bridge.Kly.twine
