import YM.Mistral.Site
import YM.Mistral.Garb
import YM.Tarn.Vance
import YM.Needle.Pond
/-!- one translation test. regulator at authentic.t signs cut preserved via MoveR, no interpolation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Hub.Duon
open Function Set Metric Filter QCD Lat Lattice UV Patria Patria.Depth
open Poised Plans Plans.Stamp Intag Intag.Vale Finset
open scoped Topology BigOperators Matrix ComplexOrder ContDiff Classical
variable {d:ℕ}{s:RawSym}(H:Vale.Laurel d)
open Needle Needle.GaugeP Hub Cells Tarn.Dispersed Lattice
variable {C:Sequence}{P:Calibration C}(Y:Landing P.sym H) (F:GaugeP P H Y)
variable {β e:ℝ}(h:C.Path β e)
include h
set_option quotPrecheck false
--
local notation "N" i:arg=> C.N i
local notation "φ" i:arg=> (C.A i).regulator
local notation "η" i:arg=>evenW C.S (C.R i) (h.even i)
local notation "Z" i:arg k:arg=> C.S.side (C.R i) k
local notation "g" i:arg=> F.heads i
local notation "ψ" p:arg i:arg=> ((stem P d i) p)
variable (i j ℓ B:ℕ)(hp:j+1≤ℓ)(hℓ:ℓ≤C.N i) (w:Label d)
local notation "Qz"=> ratioTo C.S (C.N i) j
variable (hV:P.System)
-- suppose K.fault test.K.height plus.V.Money honest
include hp h hℓ hV
lemma miles (hc:16*B+32≤ratioTo C.S ℓ j)(hJ:40*(1+1)≤ (C.S.step j).L.val)(X U:ℝ)(h1:0 ≤ X)(h2:0 ≤ U)(x b:Cover)(h_ : ratioTo C.S (C.N i) j < separation 0 (wrap (Z i (C.N i)) x))(hN:∀ t:Stokes d, GreenP C i j (F.heads i t) X)
    (hG:∀ (z:Site (Z i ℓ))(p:Site (Z i j)), (viewW C.S (C.R i) hℓ).parent (wrap _ b)∈ (Column.sky C.S (C.R i) j ℓ (Nat.le_of_lt hp) ((η i) j) z).margin p (B+1) → Gold (φ i) (Column.sky C.S (C.R i) j (C.N i) ((Nat.le_of_lt hp).trans hℓ) ((η i) j) z) p ((stem P d i) w b) U) : ‖F.heightH i x ((stem P d i) w)‖ ≤ X*U:=by
    let a:= b-x; let S0:= (φ i); let Tz:= (Z i (C.N i));
    let V:Fin (1+1)→ Site Tz:=![wrap _ b,wrap _ a]; have hx(j k:Fin (1+1))(h:j≠k): Qz< separation (V j) (V k):=by
         have ht: a+x=b:= (by unfold a; abel); have h':separation (V 1) (V 0)= separation 0 (wrap Tz x):=by change separation (wrap _ a) (wrap _ b)=_; nth_rw 1 [← ht]; rw [add_comm a,map_add,← separation_translate 0 (wrap Tz x) (wrap Tz a), zero_add] -- arg order
         have hFQ:= h_.trans_eq h'.symm
         fin_cases j<;> fin_cases k <;> first| contradiction| exact hFQ|exact hFQ.trans_eq (separation_comm ..)
    obtain ⟨z,p,Fp,hp0,hpc⟩:= housing (C.R i) (h.even i) (Nat.le_of_lt hp) hℓ V hx B hp hc hJ -- argument order H.C.X.K
    let T':= Column.sky C.S (C.R i) j (C.N i) ((Nat.le_of_lt hp).trans hℓ) ((η i) j) z
    have hg: Gold (φ i) T' (p 0) (((stem P d i) w) b) U:=hG z (p 0) hp0
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg h1 h2)).2 ?_; intro t; have hA : Gold (φ i) T' (p 1) ((F.heads i t) a) X:=hN t (hp.trans hℓ) T' rfl rfl (p 1) a (hpc 0)
    let K:=P.physical none i (F.g i t); let L:= P.physical none i w
    let f:Fin 2→ Insertion Tz 6:= ![K a,L b]; let P0 := p ∘ Fin.rev; let W0:Fin 2→ℝ:=![X,U]
    have hx:= Gold.value (R := φ i) (T := T') P0 (Fp.comp Fin.rev_injective) f W0 (by intro j; fin_cases j; exact hA; exact hg) rfl rfl ((h.normalized i).beta_pos le_rfl).le (sideW h _ _) (Needle.engaged h i)
    have h:S0.average (K a * L b)= S0.average (K 0*L x):=by
          obtain ⟨G⟩:=MoveR.marchP (φ i) rfl a
          have hv (u:Label d)(x:Cover): march a (P.physical none i u x)=P.physical none i u (x+a):=by
               unfold Calibration.physical; rw [show ∀ v:Label d,∀ p:Cover,⇑(P.candidate d Tz p v)=(fun U=>Cylinder.places p (P.localMap d v) U) from (fun x p=>funext fun k=>hV.sections.localizes ..),show ∀ v:Label d,∀ p:Cover,⇑(P.candidate d Tz p v)=(fun U=>Cylinder.places p (P.localMap d v) U) from (fun x p=>funext fun k=>hV.sections.localizes ..)] -- use simp func. verify namespace
               exact Patria.Canvas.stylus ..
          let X(k:Fin 2):= (![K 0,L x]) k; have ht:= G.skies [0,1] X f (by intro i hi; fin_cases i; exact (hv (F.g _ _) 0).trans (by rw [zero_add]; rfl); exact (hv w x).trans (by rw [show x+a=b from (by unfold a; abel)]; rfl))
          change _= _; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at ht; exact ht
    change ‖S0.average (K 0 * L x)‖≤ _; rw [← h]; simp only [List.ofFn_succ,List.prod_cons,List.ofFn_zero,List.prod_nil,mul_one,Fin.prod_univ_succ, Finset.univ_eq_empty,Finset.prod_empty] at hx; exact hx
end YM.Massive.Patria.Hub.Duon
#print axioms YM.Massive.Patria.Hub.Duon.miles
