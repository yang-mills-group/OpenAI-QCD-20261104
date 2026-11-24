import YM.QCD.Globe.Fae
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
open Trees Nola
variable (S h)
variable (P:Plan j)(H: Plan k) (i:Flavor N) {K:Sheet f}{X:EvenA f N}{x A b a d C t w η u χ v r δ y R R' W:ℝ}
noncomputable def whiskey (N:ℕ)(a b:ℝ):ℝ:= (Fintype.card Fiber:ℝ)*N*Real.log a + b +(2*(Fintype.card Fiber:ℝ)*N)*Real.log 2
set_option quotPrecheck false
local notation "D₀"=> sunny H S.land c
local notation "g"=> sliceL S h
-- parameters
abbrev Mercy (i:Flavor N)(m:ℕ)(C:ℝ):Prop:=∀ (c:Side)(X:EvenA c N)(t A:ℝ),0<t→ Cocoa X→ GrassA X t m A→ Beam (feeF i X) m (t⁻¹^2*C*A)
def ForceS (S:Flight j k)(h:f.val=c.val*S.L.val)(w:ℝ):Prop:=∀ (R:Sheet f), Drier R →∀ (t:ℝ),0 ≤ t→Beam R 6 t → Cent id id 6 (t*w) (barP S h* R*proton S h)
lemma sources (A B:Kit.Rail f c)(he:Cent (g).parent id m a A)(hp:Ton id (g).embed m b (B-A)): Cent (g).parent id m (2^m*b+a) B:=by
     have h₀:= overleaf g id (sliceL S h).embed (B-A) hp.toR; rw [show (g).parent∘(g).embed=id from ?_] at h₀; · have ht:=Cent.smul he (-1); rw [norm_neg,norm_one,one_mul,neg_one_smul] at ht; have hx:=Cent.sub h₀ (show Cent ((sliceL S h).parent ∘ id) id m a (-A) from ht); rwa [sub_neg_eq_add,sub_add_cancel] at hx
     exact funext fun i=> (g).embed_parent i -- h shadow notation? edit
structure TrailS (P:Plan j)(H:Plan k)(S:Flight j k)(h:f.val=c.val*S.L.val)(X:EvenA f N)(K:Sheet f)(t r v y T:ℝ):Prop where
 road: ∃ (X': EvenA c N)(L:Sheet c), Fused X' L t r v ∧ |mass L| ≤ y ∧ expo T f * pebble (paleF N (sunny H S.land c+L) + X') ≤ pebble (paleF N (sunny P S.wing f + K) + X)
lemma feastQ (hf: Mercy i 6 C) (hz: Beam (father S h)⁻¹ 6 w)(hp:Ton (g).embed id 6 w (barP S h))(hq:Ton id (g).embed 6 w (proton S h))(hW: ForceS S h W)(hS: Cent (g).parent id 6 R' (proton S h)) (ht:Beam D₀ 6 R) (he:1/2 ≤ sheen D₀)(hx:Fused X K (2*(Real.exp 2*x)) r a)(hk:0 ≤ A)(hT:0 ≤ t)(hr:0 ≤r)(hu:0 < u)(hu':u≤1)(hδ:0<δ)(hδ':δ ≤1)(hg:degreePriceCard (Real.exp δ-1) 1 ≤1/2)(hK: |mass K| ≤ t)(hm: t+r ≤ A)(ha: w*A≤1/2)(ho:0 ≤ η)(hy:0 < x)(hy': u⁻¹*a+x⁻¹^2*Real.exp 4*((Fintype.card (Brick.Note N):ℝ)^2*(2*(2*w)))≤ δ) (hD:0 ≤ v)(hv:v ≤1)(hi:0≤W)(hw:1 ≤ w) (hh:2^6*(2*w^2*A)+R' ≤ b)(hb:0≤ b)
      (hd: Brick.stemF N*b*(2*(2*(Real.exp 2*x))) ≤ x*v)
      (hB:d=(S.L.val:ℝ)^4*2^6*(u*(Real.exp δ-1)*2))(hb':0 ≤ d)(hl: d*v^4 ≤ a)
      (hR:2^6*(w^2*t)+r*W+2^6*(2*w^3*A^2) + ((2*(2*(Real.exp 2*x)))⁻¹)^2*C*d ≤ η)
      (hη:η ≤1/4)(hY:0≤R)(he':2*dimeZ R η ≤ r)(hU:dimeZ R η ≤ y): TrailS P H S h X K (2*(Real.exp 2*x)) r a y (whiskey N (2*w) d):=by
     constructor
     obtain ⟨M,hL,hM,hH⟩:=counting hx.tone hx.rateG
     let F:= (mass K:ℂ) • (1:Sheet f); have hz':Beam F 6 t:= (Ton.one.smul (mass K:ℂ)).up (by rw [Complex.norm_real, Real.norm_eq_abs,mul_one]; exact hK)
     have heq: K-(mass K:ℂ) • 1=M:=by
        conv_lhs=> lhs; rw [hL];
        exact add_sub_cancel_left ..
     have hv':Beam M 6 r:= Eq.subst (motive:=fun y=> Beam y 6 r) heq hx.remS; have hK':Beam K 6 A:=by nth_rw 1 [hL]; exact (hz'.add hv').up hm
     let V:= (tied S h 0 1); obtain ⟨hC₁,hC₂,hC₃,hC₄,hC₅⟩:= stern S h H K F M hL hx.tone hk hT (mul_nonneg hr hi) (zero_le_one.trans hw) (high_rank S h) hK' hz' (hW M hM r hr hv') hz hp hq ha P
     let e:=2*(Real.exp 2*x); have he₀:0<e:=by unfold e; positivity
     let Y: Sheet c:=1-V*(father S h+K)⁻¹*Vᴴ; obtain ⟨z,L,hQ,hc,hZ,hI,hJ,hσ⟩:= summationP S h X P K hx.tone hx.moo hx.cocoa hu hu' hδ hδ' hg hC₃ hC₂ hx.work hy hy' (Cent.up (sources S h _ _ hS hC₄) hh) hb hD hv (show 0 < 2*e by positivity) hd
     have hz₀:GrassA (peakZ (oilD L)) (2*e) 6 a:=by apply le_trans hJ; rw [hB] at hl; exact mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _)
     subst d
     let G:=feeF i (oilD L); let U:= peakZ (oilD L); let Y':=Y- D₀; let J:=Y'+G; have hh : oilD L=paleF N G+U := mercyR (oilD L) _ (oil₀ L) hc.flavorG; have hP: Cocoa U:=by have h:U=oilD L - paleF N G:=Eq.symm (by rw [hh]; exact add_sub_cancel_left ..); exact h ▸ hc.sub ((hc.pick i).butter _)
     have ht':Tempo J:= hC₅.add (hc.pick i)
     obtain ⟨w',_,hφ,hnu,hw',hR₀,hB'⟩:= Globe.lin U hP (Globe.forged _) hz₀ he₀ (D₀) J (savior ..) ht' ht ((hC₁.add (hf c (oilD L) (2*e) _ (by positivity) hc hI)).up hR) ho hY he hη
     let X':=wearK c N w' U; let y':=dub D₀ J w'; refine ⟨X',y', ⟨hB'.tone,hB'.rateG,hB'.remS.up he',hB'.cocoa,hB'.moo,hB'.work⟩,hR₀.trans hU,?_⟩
     have hi : c ≤ f:=by
        change c.val ≤ f.val
        exact le_trans (Nat.le_mul_of_pos_right _ S.L.property) (le_of_eq h.symm)
     have he' : paleF N Y+oilD L = paleF N (D₀+J)+U:=by rw [hh,←add_assoc, ← Port.oneC]; apply congr_arg (fun X:Sheet c=> paleF N X+U); unfold J Y'; abel
     rw [hσ] at hQ; exact fanfare (father S h+K) L _ _ _ _ hC₃ hC₂ (by linarith) hZ hb' (by positivity) hQ (by rw [show paleF N _ + _ = _ from he']; exact hw') hφ hnu hi -- h shadow
end YM.QCD.Globe
