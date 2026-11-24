import YM.Tawny.Pane
import YM.Push.STRESS_FLUX.Color
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole
local notation "T" => SpinMode d
local notation "Ae" => Pairs T
local notation "W"=>CensusA d
open Pane
noncomputable def gravel (a b: Flavor 6)(p q:Multi d): CensusA d→ₗ[ℂ]Bundle:= { toFun:=prism a b p q,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
variable (i k:Axis)(p q:Multi d)(x:Label d)(h:Quiet x.val)(hd:d≤10)(J:Labels.Jet su)(u:su.El)
local notation "A"=> colorTable (d:=d) u
local notation "U"=> touch (colour u)
local notation "μ"=> gravel a b p q
local notation "X"=> skin (d:=d) J x.val
local notation "X₀"=> skin (d:=d) (0:Labels.Jet su) x.val
local notation "L"=> glow x h hd
include h hd
lemma convey : A*X = skin (Labels.colored u J) x.val*A:=by
    calc
       _=A*(star A*(skin (Labels.colored u J) x.val*A)):=by nth_rw 1 [token J x h hd]; -- u implicit? token args
       _= _:=by rw[← mul_assoc,(pru _).2,one_mul]
lemma mirrorU : μ (skin (Labels.colored u J) x.val) * U= U*μ X:=by
    ext i j; exact Eq.trans (Eq.symm (hue_right a b p q ..)) ((congr_fun (congr_fun (convey x h hd J u).symm _) _).trans (hue_left ..)) -- ..
lemma root_color : μ X₀ = wave (Stew.gold (μ X₀)):=by
    apply Stew.gilt; intro u; have he:= mirrorU a b p q x h hd 0 u; rw [show Labels.colored u (0:Labels.Jet su)=0 from funext fun i=> map_zero (Labels.Taylor.paint u)] at he; exact he.symm
lemma ray_color (J:Labels.Taylor su 0) : μ (L (Labels.Taylor.paint u J))* U= U*μ (L J):=by
    let Tj:Labels.Jet su:=Pi.single 0 J; have ht:= mirrorU a b p q x h hd Tj u; have hu : Tj 0=J:=Pi.single_eq_same ..
    have he:=mirrorU a b p q x h hd 0 u; rw [show Labels.colored u (0:Labels.Jet su)=0 from funext fun i=>map_zero (Labels.Taylor.paint u)] at he
    rw [shiny _ x h hd,shiny Tj x h hd, show Labels.colored u Tj 0=Labels.Taylor.paint u J from congr_arg (Labels.Taylor.paint u) hu,hu,map_add,map_add,add_mul,mul_add,he] at ht; exact add_left_cancel ht
omit h hd
namespace HintR
variable (V:su.Color→ₗ[ℝ] Mat)(H:∀ u:su.El,∀ x:su.Color,V (su.adjoint u x)*colour u=colour u* V x)
local notation "C"=> su.colorMat
local notation "P"=>su.projectColor
local notation "ζ"=> Matrix.trace
-- bilinear covariance via projection traceless
variable (e:su.Color)(he:‖e‖=1)
include he H
private lemma bills (h:∀ x:su.Color,V x∈su.lie):∃ z:ℝ,∀ x,V x=z • C x:=by
   let ℒ:= P ∘ₗ V; have hr(x):V x=C (ℒ x):=(su.colorMat_project_self (h x)).symm
   have hp(u:su.El)(x:su.Color): ℒ (su.adjoint u x)=su.adjoint u (ℒ x):=by
        apply Gauge.colorMat_injective; rw [Gauge.mat_adjoint, ← hr, ← hr]; change V _ = colour u * V x * star (colour u); rw [← H,mul_assoc,show colour u * star (colour u)=1 from Gauge.mat_mul_star _ _,mul_one] -- `U` defin mismatch
   let B:su.Color→ₗ[ℝ]su.Color→ₗ[ℝ]ℂ:= { toFun:=fun x=>Complex.ofRealCLM.toLinearMap ∘ₗ (innerₛₗ ℝ (ℒ x)), map_add':=fun x y=> LinearMap.ext fun z=>by simp [inner_add_left], map_smul':=fun r x=>LinearMap.ext fun z=>by simp } -- starRing ℝ def?
   have hb(u:su.El)(x y):B (su.adjoint u x) (su.adjoint u y)=B x y:=by change (↑(inner ℝ (ℒ _) _):ℂ)=_; rw [hp,StressFlux.inner_adjoint]; rfl
   let q:= inner ℝ (ℒ e) e; refine ⟨q,fun x=>?_⟩; have hx: ℒ x=q • x:=by
        apply ext_inner_right ℝ; intro y; have hE:= StressFlux.bilinear_invariant QCD.simple B hb he x y; change (↑(inner ℝ (ℒ x) y):ℂ)=(inner ℝ x y) • (↑q:ℂ) at hE; rw[real_inner_smul_left]; exact Eq.trans (congr_arg Complex.re hE) (by simp; ring)
   rw [hr,hx,map_smul]
omit he
include H
private lemma traces(x:su.Color): ζ (V x)=0:=by
   let ψ : Mat→ₗ[ℝ]ℂ:= Matrix.traceLinearMap _ _ _; have ht(u:su.El)(x:su.Color) : V (su.adjoint u x)= colour u* V x*star (colour u):=by
       rw [← H,mul_assoc,show colour u * star (colour u)=1 from Gauge.mat_mul_star _ _,mul_one]
   have hp:= StressFlux.linear_invariant QCD.simple (ψ ∘ₗ V) (fun u x=>by change Matrix.trace (V (su.adjoint u x))=Matrix.trace (V x); rw[ht, Matrix.trace_mul_cycle, show star (colour u)*colour u=1 from Gauge.mat_star_mul _ _,one_mul]); exact LinearMap.congr_fun hp x
include he
open Complex
private noncomputable def vbar (S:Mat):=star S
lemma prismC : ∃ z:ℂ,∀ x,V x=z • C x:=by
   let τ:Mat→ₗ[ℝ]Mat:= {toFun:=vbar,map_add':=star_add,map_smul':=fun r x=> show star (r • x)=_ by rw [star_smul,star_trivial]; rfl }
   let Xm:= V-τ ∘ₗ V; let Y:= Complex.I • (V+ τ ∘ₗ V); have hx(x):Xm x= V x- star (V x):=rfl; have hy(x): Y x= Complex.I • (V x+star (V x)):=rfl
   have hw (u:su.El)(x):V (su.adjoint u x)=colour u*V x * star (colour u):=by rw[← H,mul_assoc,show colour u * star (colour u)=1 from Gauge.mat_mul_star _ _,mul_one]
   have hS(u:su.El)(x): star (V (su.adjoint u x))*colour u=colour u*star (V x):=by rw [hw,star_mul,star_star,star_mul, mul_assoc,mul_assoc, show star (colour u)*colour u=1 from Gauge.mat_star_mul _ _,mul_one]
   obtain ⟨f,hF⟩:=bills Xm (by intro u x; rw[hx,hx,mul_sub,sub_mul,H,hS]) e he (fun x=> (lie_iff _).mpr ⟨by rw[hx,star_sub, star_star,neg_sub], by rw [hx,Matrix.trace_sub,Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose,traces _ H,star_zero,sub_self]⟩)
   obtain ⟨g,hG⟩:=bills Y (by intro u x; rw[hy,hy,smul_mul_assoc,mul_smul_comm,add_mul,mul_add,H,hS]) e he (fun x=> (lie_iff _).mpr ⟨by rw[hy,star_smul,star_add, star_star,add_comm _ (V x),show star Complex.I= -Complex.I from (by simp),neg_smul], by rw[hy,Matrix.trace_smul, Matrix.trace_add,Matrix.star_eq_conjTranspose,Matrix.trace_conjTranspose,traces _ H, star_zero,add_zero,smul_zero]⟩)
   refine ⟨(2:ℂ)⁻¹ * ((↑f:ℂ)-Complex.I*(↑g)),fun x=>?_⟩
   calc V x=(2:ℂ)⁻¹ • (Xm x - Complex.I • Y x):=by rw[hx,hy,smul_smul, Complex.I_mul_I,neg_one_smul]; module
        _ = _:=by rw[hF,hG,← Complex.coe_smul f,← Complex.coe_smul g, mul_smul, sub_smul, mul_smul]; rfl
end HintR
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.HintR.prismC
