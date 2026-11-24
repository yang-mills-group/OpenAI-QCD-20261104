import YM.Portland.Roast
import YM.Portland.Coffee
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC.Brave.CoatB
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward Grass.Ovule
open YM.Next.Free QCD.Flume QCD.Globe QCD.Globe.HalfMass Finset NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A B:Type*}[Fintype A][Fintype B]{c f:Side} {n k j F:ℕ}
variable (x y:Site c)(i j:Lat.Fiber) (a b:Flavor F)
set_option quotPrecheck false
local notation "M"=> Modes c F
local notation "F!"=> Keys c F
variable (X:Spike)(D: Fields c F)(T:Flavor F→ Sheet c)
local notation "Kq"=> Cove.Keys c F
local notation "BO"=> Ovule.core (Cove.Keys c F)
variable (p q: Lat.Row c)
variable (ht:a≠b) (he: Stew.panel 2 D=form (Matrix.blockDiagonal T))
include he ht
local notation "sι"=> spr (talon b q)
local notation "s²"=> spr (graphB a p)
local notation "sp"=> spr (planeL a i)
local notation "sQ"=> spr (planeR b j)
open QCD.Comet
variable (Z:ℂ)
local notation "u"=> (Z * BO (exp D))
local notation "B₁"=> (spr (planeR b j))
noncomputable def murphy (a b:Flavor F)(i j:Lat.Fiber): Fields c F→ₗ[ℂ] ℂ := (Ovule.core _).toLinearMap.comp ((spr (planeR b j)).comp (spr (planeL a i)))
noncomputable def aroma (a b:Flavor F)(i j:Lat.Fiber)(p q:Lat.Row c) (D:Fields c F)(w:ℂ):= w⁻¹ * murphy a b i j (pairD (p,a) (q,b) D)
variable (K C0 C2 C4:ℝ)
local notation "xc"=> spinPrice Lat.g5
noncomputable def wingC (K C0 C2 C4:ℝ):ℝ:= C4+C0*(xc*K*xc*K)+ K*C2+(xc*K*xc)*C2
local notation "bc"=> wingC K C0 C2 C4
local notation "varA" p=> vary (X:=Pairs (Modes c F)) (Sum.inl (p,a))
local notation "varB" p=> vary (X:=Pairs (Modes c F)) (Sum.inr (p,b))
variable (hD:Plus D)(hZ:Z * Grass.Ovule.core (Cove.Keys c F) (exp D)≠0)
variable (hp:∃ y:Alg (Cove.Keys c F),True) -- unused drop
-- estimator per pair plus E4. normalized.L.Clock true.
variable (hk:0 ≤K)(hv:0 ≤C0)(h₂:0≤C2)(h₄:0≤ C4)(hM:Tempo (T a))(hW:∀ i x,‖stalk (T i) x‖ ≤K)
omit he ht
lemma wingPos (hk:0 ≤ K)(hv:0 ≤ C0)(h₂:0 ≤ C2)(h₄:0≤C4) :0 ≤ wingC K C0 C2 C4:=by unfold wingC; have hh:= spinPrice_nn Lat.g5; positivity
lemma fogR (D:Fields c F): ‖murphy a b i j D‖≤ bins Kq D 2:=by
     refine (peak (spr (planeL a i) D) (planeR b j) (fieldV _ _ (fun _=> (plane_cost _).le)) 0).trans (peak _ (planeL a i) (fieldV _ _ fun x=> ?_) 1)
     simp only [comp_apply,norm_star]; exact (plane_cost _).le
include he ht hD hZ hM hW hk hv h₂ h₄
local notation "ρq"=> (Z • exp D)
set_option maxHeartbeats 600000
set_option pp.universes false
lemma jumper (Y:Insertion c F)(h:QCD.Comet.BreezeX (Z • exp D) C0 C2 C4 Y): ‖aroma a b i j p q (Y 1) (Z*BO (exp D))‖ ≤ bc + C0*bins Kq (pairD (p,a) (q,b) D) 2:=by
    obtain ⟨Q,hQ,hx,h0,h2,h4⟩:=h.owns
    have hA:= braidF a b D T p q ht he; have h2':= braidC i j a b D T ht he
    let t:=pairD (p,a) (q,b); let e:= murphy a b i j (c:=c); have hξ(v:Fields c F) : t v=s² (sι v):=by unfold talon graphB; rw [unitV,unitV]; rfl
    have hz(v:Fields c F): e v= BO (sQ (sp v)):=rfl
    have he': aroma a b i j p q (Y 1) (Z*BO (exp D)) = e (t Q) + BO Q * (e (t D)+ BO (sp (s² D))* BO (sQ (sι D))) + BO (sQ (sι D))* BO (sp (s² Q))+ BO (sp (s² D))* BO (sQ (sι Q)):=by
         unfold aroma; rw [hx,smul_mul_assoc,map_smul,map_smul,hz,hξ,eon D Q (planeR b j) (talon b q) (graphB a p) (planeL a i) hD hQ hA (braidB j a b D T p he) (braidA i a b D T q he) h2']; simp only [smul_eq_mul]; rw [←mul_assoc Z,inv_mul_cancel_left₀ hZ,hz,hz,hξ,hξ]
    have htP:‖BO (sQ (sι D))‖ ≤ K:= (abroad j b D T q he).trans (hW ..)
    let L:= xc*K*xc; have hX': ‖BO (sp (s² D))‖≤L:=(ahead i a D T p he).trans ((ring_cost (T a) hM p.1).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hW ..) (spinPrice_nn _)) (spinPrice_nn _)))
    have hF':0≤L:=by unfold L; have h:=spinPrice_nn Lat.g5; positivity
    have he:‖e (t Q)‖≤C4:=(fogR i j a b (t Q)).trans ((oneB _ ((varB q) Q) 2).trans ((oneB _ Q 3).trans h4))
    have hp:‖BO (sp (s² Q))‖ ≤ C2:=by unfold graphB; rw[unitV]; apply (le_trans (_ : _≤ bins Kq ((varA p) Q) 1) ((oneB _ _ 1).trans h2)); exact peak _ (planeL a i) (fieldV _ _ (fun x=> by rw [comp_apply,norm_star]; exact (plane_cost _).le)) 0
    have hq: ‖BO (sQ (sι Q))‖≤C2:=by unfold talon; rw [unitV]; exact (peak _ (planeR b j) (fieldV _ _ (fun x=>(plane_cost _).le)) 0).trans ((oneB _ _ 1).trans h2)
    rw [he']; calc
       _ ≤ ‖e (t Q)‖ + ‖BO Q * _‖ + ‖BO (sQ (sι D))* BO (sp (s² Q))‖ + ‖BO (sp (s² D))* BO (sQ (sι Q))‖:= (norm_add_le ..).trans (add_le_add_left ((norm_add_le ..).trans (add_le_add_left (norm_add_le ..) _)) _)
       _ ≤ C4 + C0*(bins Kq (t D) 2+ L*K) + K*C2+ L*C2:= by rw [norm_mul,norm_mul,norm_mul]; refine add_le_add (add_le_add (add_le_add he (mul_le_mul h0 ?_ (norm_nonneg _) hv)) ((mul_le_mul htP hp (norm_nonneg _) hk))) (mul_le_mul hX' hq (norm_nonneg _) hF'); exact (norm_add_le ..).trans (add_le_add (fogR ..) (by rw[norm_mul]; exact mul_le_mul hX' htP (norm_nonneg _) hF'))
       _ = _:=by dsimp only [L,t, wingC]; ring
-- Flavor selection actual starts only. Output certificate includes dedicated total charge families.
end YM.Massive.PCAC.Brave.CoatB
#print axioms YM.Massive.PCAC.Brave.CoatB.jumper
