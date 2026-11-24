import YM.Heron.Pike
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
open Arise.Range
open Maxwell.Free (fromCenter)
open Finset
variable {d:ℕ}(α β:letters d)(x:Points 2)(y:E4)(hx:x∈conf 2)(hy:Points.cons y x∈conf 3)
local notation "A"=> chime (hill d) (Points.cons y x)
local notation "S"=> Dot d
variable (p q:GPol)(u v:List (letters d))
noncomputable def ballow (p q:GPol)(u v:List (letters d)):Fin 2→ Pol d:= ![p⊗ₜ[ℂ] Hail.tagD u,q⊗ₜ[ℂ] Hail.tagD v]
local notation "P"=> Hail.tagD u
local notation "Q"=> Hail.tagD v
local notation "W"=> tot u v
local notation "G"=> Maxwell.Wick.moment su
local notation "B"=> ballow p q u v
noncomputable abbrev ester(x: Points 2)(p q:GPol):ℂ:= Maxwell.Wick.moment su x (![Maxwell.reduceEq p, Maxwell.reduceEq q])
local notation "E"=> ester x p q
local notation "C"=> fiesta x
local notation "Ω"=> trioL y x B
variable (i j:letters 8)
noncomputable def colorJ (x:Points 2)(y:E4)(i:letters 8)(s:Dot d):ℂ:= linked (x s.1) y s.2 i
local notation "κ"=> colorJ x y
include hx hy
lemma toys : Ω ((1:GPol)⊗ₜ[ℂ] (atom i*atom j))= - slips W (fun a z=> slips z (fun b w=> (κ i a *κ j b)* (E*C w))) :=by
    have ht(l:letters 8): twig (hill d) 0 (atom l)=line (tipR d l):=ExteriorAlgebra.map_apply_ι _ _; rw [show trioL y x (ballow p q u v) ((1:GPol)⊗ₜ[ℂ] (atom i*atom j))= G (Points.cons y x) (![Maxwell.reduceEq (1: GPol),Maxwell.reduceEq p,Maxwell.reduceEq q])*lease A ((line (tipR d i)*line (tipR d j))*pwn ((tot u v).map (west d))) from ?_]; -- right side _ _ placeholders
    swap
    · refine (build x y hx hy p q u v (atom i*atom j) 1).trans (congr_arg (_ * ·) (congr_arg _ (congr_arg (· * _) (?_)))); exact (map_mul (twig (hill d) 0) _ _).trans (congr_arg₂ (·*·) (ht i) (ht j)) -- placeholders fix
    rw [map_one,show G _ (![1, Maxwell.reduceEq p, Maxwell.reduceEq q])= E from (Maxwell.Wick.adjoin hx y _).symm] -- direction fix
    rw [mul_assoc (line _) (line _), spin_pulls A (west d) W (tipR d i) (tipR d j) (quiets _ hy 0 _ _)]; unfold slips; rw [mul_neg]; refine congr_arg Neg.neg ?_; simp_rw[drink x y hx hy, auxili x y hx hy, neg_mul_neg,smul_eq_mul,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; try rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; unfold colorJ fiesta; ring -- fix
variable (a b: Axis)(f:Flavor 6)(D:Spike)(m n:Multi 8)(k: Hue)
noncomputable def crossG (f:Flavor 6)(a:Axis)(l r:Multi 8)(x:Points 2)(y:E4)(Az Bx:Dot d):ℂ:= ∑ k: Hue,∑ i:Pinor,∑ j:Pinor,gamma a i j* (colorJ x y (code true l i k f) Az * colorJ x y (code false r j k f) Bx)
local notation "I★"=> (0:Multi 8)
noncomputable def beeD (f: Flavor 6)(a b:Axis)(x: Points 2)(y:E4)(Az Bx:Dot d) := (crossG f a 0 (UV.first b) x y Az Bx-crossG f a (UV.first b) 0 x y Az Bx)+(crossG f b 0 (UV.first a) x y Az Bx-crossG f b (UV.first a) 0 x y Az Bx)
noncomputable def gustD (d:ℕ)(p q:GPol)(x:Points 2)(w:List (Dot d)) : (Dot d→Dot d→ℂ) →ₗ[ℂ] ℂ := { toFun:=fun f=> slips w (fun a z=>slips z (fun b s=> f a b*(ester x p q* fiesta x s))), map_add':=by intro f g; unfold slips; simp_rw[Pi.add_apply, add_mul, smul_add, Finset.sum_add_distrib,smul_add, Finset.sum_add_distrib], map_smul':=by intro v g; unfold slips; simp_rw [Pi.smul_apply,_root_.smul_mul_assoc,Finset.smul_sum]; simp only [smul_comm v, RingHom.id_apply] }
lemma spawn (k:Hue)(i j:Pinor) : trioL y x B ((1:GPol)⊗ₜ[ℂ] (bar ((m,i,k),f)*psi ((n,j,k),f)))= -gustD d p q x W (fun c c'=>κ (code true m i k f) c *κ (code false n j k f) c'):= toys x y hx hy p q u v ..
lemma spinDance : trioL y x B (UV.bilinear f f (gamma a) m n)= -gustD d p q x W (crossG f a m n x y):=by
    unfold bilinear; simp_rw [TensorProduct.tmul_sum, TensorProduct.tmul_smul,map_sum,map_smul,fun i j k=>spawn (x:=x) (y:=y) hx hy p q u v f m n k i j]; let P'(i j:Pinor)(k:Hue) (a b:Dot d):ℂ:=κ (code true m i k f) a*κ (code false n j k f) b
    have he : crossG (d:=d) f a m n x y=∑ i:Pinor,∑ j:Pinor,∑ k:Hue,gamma a i j • P' i j k:=by
           funext r s; simp only[Finset.sum_apply,Pi.smul_apply]; change (∑ k:Hue,∑ i:Pinor,∑ j:Pinor,_)=_; rw[Finset.sum_comm]; apply sum_congr rfl; intro i _; rw[Finset.sum_comm]; rfl
    rw [he]; simp only[_root_.map_sum,map_smul,smul_neg, Finset.sum_neg_distrib]; rfl
lemma liftBD : trioL y x B (((Massive.Tawny.Cast.Carnal.sunS f).val (a,b)).val)= - slips W (fun i z=> slips z (fun j w=> beeD f a b x y i j * (E* C w))) :=by 
    rw[Massive.Tawny.Cast.TableT.W_sun,Submodule.coe_add,map_add,Massive.Tawny.Cast.Carnal.amt,Massive.Tawny.Cast.Carnal.amt]
    unfold spinStressUnsymm; simp_rw [map_sub, spinDance x y hx hy]; let B':= beeD (d:=d) f a b x y
    have he:B'= crossG f a 0 (UV.first b) x y-crossG f a (UV.first b) 0 x y+(crossG f b 0 (UV.first a) x y-crossG f b (UV.first a) 0 x y):= rfl
    change _= -gustD d p q x W B'; rw [he,map_add,map_sub,map_sub]; abel
end YM.Heron
#print axioms YM.Heron.toys
#print axioms YM.Heron.liftBD
