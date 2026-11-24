import YM.Mural.Colt
/-! # Business laws, independent of coefficient sum signs -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.PaletteT
open QCD QCD.Grass QCD.Creek Cupola QCD.Cove QCD.Sway QCD.Sway.OrbitG Function Finset Filter MeasureTheory NormedSpace
open Plate Stitch Tablet Ribbon Lattice Wilson Lat
open scoped BigOperators Topology Classical ContDiff
variable {E P:Type*}{I A:Type} [Fintype I]{N:ℕ}
abbrev Delta (I:Type):= Matrix (Option I) (Option I) ℂ
def straight (K:Delta I):Prop:=∀ i:Option I,∑ j,K i j=1
variable (K:Delta I)
-- any two arrays. at any specified gauge.Must keep `Sways` continuous ℂ-linear.
section generic
variable {A:Type*}[NormedCommRing A] [NormedAlgebra ℂ A](H:A→ₐ[ℂ]A) {x x' y y': Option I→A}
def Binds (x y: Option I→A):Prop:=∀ i,H (x i)=aggregate (fun j=> K i j) y
lemma binds_pin (p:A)(x y:Option I→A)(h:Binds K H x y)(φ:ℂ) : Binds K H (fun i=> φ • x i) (fun i=> φ • y i):=by
   intro i; rw [map_smul,h i]; unfold aggregate; rw [smul_sum]; exact sum_congr rfl fun j _=> smul_comm ..
lemma unity (h:straight K)(f:A)(g:A)(he:H f=g) : Binds K H (fun _=>f) (fun _=>g):=fun i=>he.trans (aggregate_one _ (h i) _).symm
lemma binds_up (hf:Binds K H x y)(hg:Binds K H x' y') : Binds K H (fun i=> x i+x' i) (fun i=>y i+y' i):=fun i=>by rw [map_add,hf i,hg i]; unfold aggregate; simp_rw [smul_add,sum_add_distrib]
lemma binds_mul (hh : straight K)(hf:Binds K H x y)(hg:Binds K H x' y')(h:∀ i j,(y i-y none)*(y' j - y' none)=0): Binds K H (x*x') (y*y'):=fun i=> by simp only [Pi.mul_apply,map_mul,hf i,hg i]; exact aggregate_mul _ (hh _) h -- explicit args
lemma binds_prod (F:Submodule ℂ (Option I→ A))(hu:(fun _=>1)∈F)(ha:∀ y∈ F,∀ z∈ F,y*z∈F)(hb:∀ y∈ F,∀ z∈ F,∀ i j,(y i-y none)*(z j-z none)=0) (f g:E→ Option I→A) (s:Finset E)(hf:∀ i∈s,g i∈F)(hc:∀ i∈s,Binds K H (f i) (g i)) (h:straight K) : Binds K H (fun i=>∏ j∈s,f j i) (fun i=> ∏ j∈s, g j i):=by
   suffices hp: ∀ u⊆s,Binds K H (fun i=> ∏ j∈u,f j i) (fun i=> ∏ j∈u,g j i)∧ (fun i:Option I=>∏ j∈u,g j i)∈F from (hp s (Subset.refl _)).1
   intro u; induction u using Finset.induction_on with
   | empty=>intro ha; simp only [prod_empty]; exact ⟨unity K H h 1 1 (map_one _),hu⟩
   | insert i u hi ih=> intro hU; obtain ⟨hx,hY⟩:= ih ((Finset.subset_insert ..).trans hU); simp only [prod_insert hi]; have he:=hU (mem_insert_self ..); exact ⟨binds_mul K H h (hc _ he) hx (hb _ (hf i he) _ hY), ha _ (hf i he) _ hY⟩
noncomputable def alphabet : Submodule ℂ ((Option I→A)×(Option I→A)) where
  carrier := {p|Binds K H p.1 p.2}
  zero_mem' := fun _=> by simp [aggregate,map_zero]
  smul_mem' c _ hx:= binds_pin K H 0 _ _ hx c
  add_mem' := fun {_ _} h g=> binds_up K H h g
lemma binds_sum (s:Finset E)(f g:E→Option I→A)(h:∀ i∈s,Binds K H (f i) (g i)) : Binds K H (fun i=> ∑ j∈s,f j i) (fun i=> ∑ j∈s,g j i):=by
    intro i; rw [map_sum]; simp_rw [aggregate, Finset.smul_sum]; rw [sum_comm]; apply sum_congr rfl; intro j hj; exact h j hj i
variable [FiniteDimensional ℂ A] -- FiniteDim for contour. Ambient top completeness
lemma binds_tsum (f g:E→Option I → A)(h:∀ i,Binds K H (f i) (g i))(he:∀ i,Summable (fun j=>f j i))(hp:∀ i,Summable (fun j=> g j i)) : Binds K H (fun i=> ∑' j,f j i) (fun i=> ∑' j,g j i):=by
    -- maps via ℂ clm & uniqueness using H finite
    intro i; let x(j:E):= fun k : Option I=> K i k • g j k
    let t(k):= K i k • ∑' j,g j k
    have hj:HasSum (fun j=>∑ k, x j k) (∑ k:Option I,t k):=by
        exact hasSum_sum (s:=univ) fun k _=> (hp k).hasSum.const_smul (K i k) -- edit
    have hSa:= H.toLinearMap.toContinuousLinearMap.hasSum (he i).hasSum
    exact (hSa.congr_fun fun j=>(h j i).symm).unique hj
lemma binds_exp (F:Submodule ℂ (Option I→ A))(hu:(fun _=>1)∈F)(ha:∀ y∈F,∀ z∈F,y*z∈F)(hb:∀ y∈F,∀ z∈F,∀ i j,(y i-y none)*(z j-z none)=0)(hf:Binds K H x y)(hc:straight K)(hX:y∈F):
    Binds K H (fun i=> exp (x i)) (fun i=> exp (y i)):=by
   have h n:Binds K H (x^n) (y^n)∧ y^n∈F:=by induction n with
               | zero=>rw [pow_zero,pow_zero]; exact ⟨unity K H hc 1 1 (map_one _),hu⟩
               | succ n h=> rw [pow_succ,pow_succ]; exact ⟨binds_mul K H hc h.1 hf (hb _ h.2 _ hX), ha _ h.2 _ hX⟩
   let f n i:= ((n.factorial:ℂ)⁻¹) • x i ^ n; let g n i:= ((n.factorial:ℂ)⁻¹) • y i ^ n
   have hx(i):HasSum (fun j:ℕ=> f j i) (exp (x i)):=exp_series_hasSum_exp' _
   have hy(i):HasSum (fun j:ℕ=> g j i) (exp (y i)):=exp_series_hasSum_exp' _
   convert! binds_tsum K H f g (fun i=>?_) (fun i=>(hx i).summable) (fun i=>(hy i).summable) using 1
   · ext j; exact (hx j).tsum_eq.symm
   · ext j; exact (hy j).tsum_eq.symm
   have hg:= binds_pin K H 1 _ _ (h i).1 ((i.factorial:ℂ)⁻¹); simpa only [Pi.pow_apply] using hg
end generic
variable [Fintype A]
lemma live_pow (q:Unit→Bool)(h:Option I→Patio (A⊕Spine Unit))(hp:Loose q h): Loose q (fun i=>exp (h i)):=by
    let F:=graph (P:=I) q A; have hh(n:ℕ):h^n∈F:=by induction n with
                    | zero=> rw [pow_zero]; exact Loose.oneV I A q
                    | succ n ih=> rw [pow_succ]; exact Loose.light (show Loose _ _ from ih) hp
    have hv (n:ℕ): (fun i=> ((n.factorial:ℂ)⁻¹) • (h i)^n ) ∈ F :=by
          have ht:= F.smul_mem ((n.factorial:ℂ)⁻¹) (hh n); convert! ht using 1
    apply F.closed_of_finiteDimensional.mem_of_tendsto (show HasSum (fun n:ℕ=> fun i=> ((n.factorial:ℂ)⁻¹) • (h i)^n) (fun i=>exp (h i)) from ?h) (Eventually.of_forall fun i:Finset ℕ=>Submodule.sum_mem _ fun n _=> hv n)
    case h=>
     apply tendsto_pi_nhds.mpr; intro i; simp_rw [Finset.sum_apply]; exact show HasSum _ (exp (h i)) from exp_series_hasSum_exp' _
end YM.MassiveQCD.PaletteT
#print axioms YM.MassiveQCD.PaletteT.binds_exp
#print axioms YM.MassiveQCD.PaletteT.live_pow
