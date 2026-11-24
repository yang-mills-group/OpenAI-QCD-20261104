import YM.QCD.Stem.Teak
/-! # Satellite stencil without Ω
 Native sizes Tick. Lift exact along offsets. No area truncation heuristics. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stem
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove -- ?
variable {C:Side}{D D' w j:ℕ}{d r t t' p p':ℝ}{B:BudgetPoint}
open Entr Villa Port Fork Grove
open Leaf Tee LeafM Rudder Revolve Sway Eyrie
variable {k m:ℕ}{a A:ℝ}
lemma ripple {Z:I→Bloom k}(hx:Fractal Z a A)(ξ:ℝ)(hp:0<ξ)(he:ξ≤1)(ha:0<a)(v:Strut f)(p:Spike)(u:Site f→ℂ)(ht:Warrant v u p)(W:Grid f):
   wild (frosting Z) ξ f (sky v W)= aura (haze v p u) (wild (frosting Z) ξ f W):=by
    let H:=wild (frosting Z) ξ f
    obtain ⟨d,hd⟩:= shades 1 (0:Site f) 0 v.2
    let t: Strut f:=(1,v.2); let V:Strut f:=(v.1,0)
    have hv : Warrant t d 1:=⟨hd,Swing.none⟩
    have hf:H (sky t W)=aura (haze t 1 d) (H W):=by
       obtain ⟨F,hF⟩:=auraCL (haze t 1 d)
       unfold H LeafM.wild; rw [← hF,F.map_tsum]; rotate_left; · exact (earns W (coined (a/(1+k)) (by positivity) hx (by rw [div_mul_cancel₀ _ (by positivity)])) hp he (by positivity)).of_norm
       refine tsum_congr fun i=> by rw [hF]; exact transferring _ _ _ _ d hd -- syntax
    have hg : Strut.pod t V=v:=by ext1 <;> simp [V,t,pod,affine]
    let e:=ink V; let P:= sat V; have hk:Warrant V e P:= assured _
    have hi := solidly (n:=f) Z hx hp he ha
    have ht':Warrant (pod t V) u p:=hg.symm ▸ ht
    change H (sky v W)=aura _ (H W); rw [← hg, ←skying, hidden_p (pod t V) u (coin V d e) _ _ ht' (comb hv hk), show H (sky V (sky t W))=aura (haze V P e) (H (sky t W)) from hi.port (sky t W) v.1 e P hk.1 hk.2, hf, combined]; rw [beset]
variable {P η z:ℝ}
lemma riseL {X:I→Bloom k}(hy:Fractal X a P)(hp:0<η)(ht:η ≤1)(hr:0<a) (H: Own c p t m (wild (frosting X) η c) r):∃ Γ Y, Run.Pack id id p t m (wild (frosting X) η c) r Γ Y ∧ Torch Γ :=by
    let p:=singleR c; let S:= wild (frosting X) η c
    have ht':Tow p (sun p) (sun p) S:= ⟨fun s g T U hh=> by have hx:=ripple hy η hp ht hr (raise p s) T g hh U; exact hx⟩
    have hx : (fun U=> foldH (S U))=S:=by funext i; let Q:= S i; change chirality c*star Q*chirality c=_; exact (by nth_rw 2 [← chi_star (n:=c)]; exact ((solidly X hy hp ht hr (n:=c)).lane i).symm ) -- rw may both Q
                                            -- edit
    obtain ⟨Γ,Y,hB⟩:= H; obtain ⟨Γ,Y,H,L⟩:= honors hB ht'; exact carry H L hx
lemma guest {T:I→Bloom n} (hm:Fractal T t p) (Y: Window f C D)(d) (hd:Quaint Y d)(hp:0<t)(hz:0<z)(hq:z ≤1)(U:Grid f): wild (frosting T) z C (Y.links U)*stream Y d=stream Y d*wild (frosting T) z f U:=by
   have hx := coined (t/(1+n)) (by positivity) hm (by rw [div_mul_cancel₀ _ (by positivity)])
   have hk {m:Side}(U:Grid m):Summable fun i=>trackP (frosting T i) z _ U :=(LeafM.earns U hx hz hq (by positivity)).of_norm
   let P: Sheet C→L[ℂ] Rail C f:=LinearMap.toContinuousLinearMap {toFun:=fun M=>M*stream Y d,map_add':=fun _ _=>Matrix.add_mul ..,map_smul':=fun _ _=>Matrix.smul_mul ..}
   let Q: Sheet f→L[ℂ] Rail C f:=LinearMap.toContinuousLinearMap {toFun:=fun M=>stream Y d*M,map_add':=fun _ _=>Matrix.mul_add ..,map_smul':=fun _ _=>Matrix.mul_smul ..}
   change P _=Q (wild (frosting T) z f U); unfold LeafM.wild; rw [P.map_tsum (hk (Y.links U)),Q.map_tsum (hk U)]; refine tsum_congr fun i=>?_ ; let b:= frosting T i; change yard b z (Y.links U) * routeM 0 (Y.links U) b.tail * stream Y d=stream Y d*(yard b z U*routeM 0 U b.tail); rw [Matrix.mul_assoc,ray_paths hd, ← Matrix.mul_assoc]; unfold yard; rw [peered Y d _ _ (Equiv.refl _) (fun x=> satin b x z U) (fun x=> rfl) (fun x=>?_),Matrix.mul_assoc] -- edit
   simp only [Equiv.refl_apply,satin,pulp,Slot.atSite,Y.expansion]

variable {hc:C.val=c.val*D}(x : Site C→ℂ)
set_option quotPrecheck false
local notation "L" => normal (Deck.divides hc) hc
local notation "P₁"=> deck (L) (Deck.divides hc) rfl x
open Collum
variable (W:Silo C)(S:BankP C){u v b:ℝ} {Z:I→Bloom n}
local notation "V"=> fun c=>wild (frosting Z) b c
local notation "W₁"=> Collum.cloud (P₁) W j w
lemma spreadsN (H:Quaint (L) x)(he:Fractal Z a u)(hv:0<a)(hl :0<b)(hm:b≤1)(ht:Run.Pack id id v t j (V C) d W S)(hz:4*w+3<c.val)(hq: Torch W)(hp:0 ≤ t)(hV:0<v) : (Run.Pack id id v t j (V c) d W₁ ((P₁).payC S j w) ∧ Torch W₁) ∧ ∀ (i:Site C)(U:Grid c), axes (L) x N ((rat W N w).view i ((L).links U))=(rat W₁ N w).view ((L).cut i) U:=by
    let s:= deck (L) (Deck.divides hc) rfl x
    have hh: Receives s (V C) (V c):= by
       refine ⟨(L).fold,fun i=>?_,fun U i j=>rule L x H _ _ (guest he L _ H hv hl hm U) i j⟩; rcases H.sign i with h|h<;>change ‖x i‖=_ <;>rw [h]<;>simp
    refine ⟨⟨s.plates W S j w ht hz hh hp,s.holds hq.1 (tucks L _ rfl x H) j w,s.wax j w W hq.2⟩,fun i U=>?_⟩
    have hk: batch (singleR c) (W₁) ((L).cut i) none w (settled U)=(stream (L) x)ᴴ* batch (singleR C) W i none w (settled ((L).links U))* stream (L) x:= forge s L hh ht hq.1 (litter L _ rfl x H) hz _ _ rfl (fun i=>Eq.symm (monotype i)) (fun i=>Eq.symm (monotype i)) U i hV
    rw [sleepX,carry_ψ, sleepX,hk]
end YM.QCD.Stem
