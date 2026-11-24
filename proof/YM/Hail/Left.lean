import YM.Hail.Litre
import YM.DawnS.Dwelling
import YM.Alum.Sip
set_option autoImplicit false
noncomputable section
namespace YM.Hail
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical
variable {d e:ℕ}(a b i l j:Axis)(x:Points 2)(hx:x∈conf 2)
noncomputable abbrev petals {A:ℕ→Type*}(p:A d)(q:A e) : (i:Fin 2)→ A (![d,e] i) := Fin.cons p (Fin.cons q (fun t:Fin 0=>Fin.elim0 t)) -- needs annotation
noncomputable def prism (K:MultilinearMap ℂ (fun i:Fin 2=>Pol (![d,e] i)) ℂ) : Pol d→ₗ[ℂ] Pol e →ₗ[ℂ] ℂ where
  toFun p:= K.toLinearMap (petals (A:=Pol) p (0:Pol e)) 1
  map_add' p q:=by
       apply LinearMap.ext; intro v; change K (update _ _ _)=K (update _ _ _)+K (update _ _ _); have h(f:Pol d)(g:Pol e):update (petals (A:=Pol) f (0:Pol e)) (1:Fin 2) g= update (petals (A:=Pol) (0:Pol d) g) 0 f:=by funext i; fin_cases i<;>simp[petals]
       simp only[h]; exact K.map_update_add (petals (0:Pol d) (show Pol e from v)) 0 p q
  map_smul' z p:=by
       apply LinearMap.ext; intro v; change K (update _ _ _)=z*K (update _ _ _); have h(f:Pol d)(g:Pol e):update (petals (A:=Pol) f (0:Pol e)) (1:Fin 2) g= update (petals (A:=Pol) (0:Pol d) g) 0 f:=by funext i; fin_cases i<;>simp[petals]
       rw[h,h]; exact K.map_update_smul (petals (0:Pol d) (show Pol e from v)) 0 z p
noncomputable def dual (d e:ℕ)(x:Points 2):= prism (moment (![d,e]) x)
local notation "K" => moment (![d,e])
local notation "W" => dual d e
lemma valD (p:Pol d)(q:Pol e): dual d e x p q= moment (![d,e]) x (petals (A:=Pol) p q):=by
    change K x (update _ (1:Fin 2) _)=_; apply congr_arg; funext i; fin_cases i <;> simp [petals]
variable (p:Pol d)(q:Pol e)
include hx
lemma aliveD : ContDiffAt ℝ ω (fun x:Points 2=>dual d e x p q) x:= by simp only[valD]; exact Sip.smoothC hx _ _
lemma fond : DifferentiableAt ℝ (fun x:Points 2=>dual d e x p q) x:= (aliveD x hx p q).differentiableAt (by simp)
local notation "c" => Points.direction (0:Fin 2) j
noncomputable def rayL (d e:ℕ) : Pol d →ₗ[ℂ] Pol e →ₗ[ℂ] ℂ where
  toFun p:={ toFun:=fun q=> Analysis.D c (fun x=> dual d e x p q) x, map_add':=by
                  intro q Q; unfold Analysis.D; simp only [map_add]; rw[fderiv_fun_add (fond x hx ..) (fond x hx ..)]; rfl, map_smul':=by
                  intro z q; unfold Analysis.D; simp only[map_smul,smul_eq_mul,RingHom.id_apply]; rw[fderiv_const_mul (fond x hx p q)]; rfl }
  map_add' p P:=by
      apply LinearMap.ext; intro q; change fderiv ℝ (fun x:Points 2=> (dual d e x) (p+P) q) _ _=fderiv ℝ _ _ _+fderiv ℝ _ _ _; simp only[map_add,LinearMap.add_apply]; rw[fderiv_fun_add (fond x hx ..) (fond x hx ..)]; rfl
  map_smul' z p:=by
      apply LinearMap.ext; intro q; change fderiv ℝ (fun x:Points 2=> (dual d e x) (z • p) q) _ _= z * fderiv ℝ _ _ _; simp only[map_smul,LinearMap.smul_apply,smul_eq_mul]; rw [fderiv_const_mul (fond x hx p q)]; rfl
lemma D_ray : rayL j x hx d e p q= D c (fun z:Points 2=>dual d e z p q) x:=rfl -- argument order x before d?
variable (g h:GPol)(f:SpinPol d)(r:SpinPol e)
noncomputable def spins (d e:ℕ)(x:Points 2)(f:SpinPol d)(r:SpinPol e):ℂ:= lease (chime (![d,e]) x) ((twig (![d,e]) 0 f)*(twig (![d,e]) 1 r))
lemma splitted : W x (g⊗ₜ[ℂ] f) (h⊗ₜ[ℂ] r) = Maxwell.Wick.moment su x (![Maxwell.reduceEq g, Maxwell.reduceEq h])* spins d e x f r:=by
     let G:Fin 2→GPol:= ![g,h]; let H:= petals (A:=SpinPol) f r; have he:(petals (A:=Pol) (g⊗ₜ[ℂ] f) (h⊗ₜ[ℂ] r))= (fun i=>G i⊗ₜ[ℂ]H i):=by funext i; fin_cases i<;>rfl
     rw[valD,he, stroll x hx G H]; refine congr_arg₂ (·*·) ?_ ?_; · apply congr_arg; funext i; fin_cases i<;>rfl
     unfold spins; apply congr_arg; rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_singleton]; rfl
end YM.Hail
#print axioms YM.Hail.D_ray
#print axioms YM.Hail.splitted
