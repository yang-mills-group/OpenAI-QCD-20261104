import YM.QCD.Globe.Twist
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
open Nola Brick Trees
variable (P:Plan 4) (i:Flavor N){a v t C T b r δ:ℝ}{L:Side}
lemma earns (hp:v≤t):expo t c ≤ expo v c:= Real.exp_monotone (mul_le_mul_of_nonpos_left hp (neg_nonpos.mpr (Nat.cast_nonneg _)))
lemma vaultM (hp:FawnP P b t T)(he:0<b)(ht:0 ≤ T)(hr:0≤r)(hv:r ≤ t)(K:Side)(ha:0 < a):∃ C:ℝ,1≤C∧∀ (c:Side)(w R:ℝ)(X:EvenA c N)(U:Train 4)(M:Sheet c),Fused X M w r R → |mass M| ≤ T→ (c=K∨ a ≤ |mass M|) → let D:=sunny P U c+M; IsUnit D.det∧Beam D⁻¹ 0 C:=by
     obtain ⟨u,hh,H⟩:=maxW P hp he _ K rfl a ha; obtain ⟨x,hx,hX⟩:= bounces P 6; obtain ⟨C,hC,H'⟩:=thickV (x+T+r) u (by positivity) (zero_le_one.trans hh)
     refine ⟨C,hC,fun c w R X z M hv' hk hB=>?_⟩; obtain ⟨B,hG,hP,hQ⟩:=counting hv'.tone hv'.rateG; let F:= sunny P z c; let f:ℂ:=mass M; let d:=F+f • 1+B;
     have hs:Beam B 6 r:=by
         have hm:= hv'.remS
         nth_rw 1 [hG] at hm; rwa [add_sub_cancel_left] at hm
     obtain ⟨hf,hD⟩:=H _ B z (mass M) hQ (hs.up hv) hP hk hB
     have hY : F+M=d:=by nth_rw 1 [hG]; rw [← add_assoc]
     intro D; unfold D; rw [hY]; have hΨ:Beam d 6 (x+T+r):=((hX z c).add ((Ton.one.smul f).up (by unfold f; rw [Complex.norm_real,Real.norm_eq_abs,mul_one]; exact hk))).add hs; exact ⟨hf,H' c d hΨ hD hf⟩
lemma rhaps (hv:0 ≤ a)(hp:T ≥2*a)(h:f.val=c.val*L.val)(hL:3 ≤ L.val):expo T f ≤ expo a f * expo T c:=by
   unfold expo; rw [←Real.exp_add]; apply Real.exp_monotone; let A:ℝ:=Fintype.card (Site f); let D:ℝ:= Fintype.card (Site c); have hh:0 ≤ D:=Nat.cast_nonneg _; change -A*T ≤ -A*a+ -D*T
   have ht:0 ≤ T:=by linarith
   have he : (L.val:ℝ) ≥ 3:=by exact_mod_cast hL
   have hg:A=D*(L.val:ℝ)^4:=by unfold A D; rw [site_card,site_card,h]; push_cast; ring
   have hk:2*D ≤ A:=by rw [hg,mul_comm]; gcongr; nlinarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤3) he 4]
   nlinarith only [mul_le_mul_of_nonneg_right hk ht,mul_le_mul_of_nonneg_left hp (show 0≤A from Nat.cast_nonneg _)]
structure Wins (P:Plan 4)(B:Side)(N:ℕ)(t r a T W:ℝ):Prop where
 per (x:EvenA B N)(y: Train 4)(K:Sheet B): Fused x K t r a→ |mass K| ≤ T→expo W B ≤ pebble (paleF N (sunny P y B+K)+x)
lemma keeper (P:Plan 4) (N:ℕ)(i:Flavor N):∃ L₀ B:ℕ,∀ L:Side,L₀ ≤ L.val→Odd L.val→3 ≤L.val→∀ F:Side,B≤F.val→∃ r T v:ℝ,0<r∧0 < T∧0<v ∧ ∀ᶠ t:ℝ in atTop, ∃ W:ℝ,0 ≤ W∧∀ k:ℕ, Wins P (F*L^k) N (2*(Real.exp 2*t)) r v T W:=by
     obtain ⟨C,d,T,hC,hd,hT,H⟩:= area_sol P; obtain ⟨L,B,hp⟩:= rails P i d T hd hT
     refine ⟨L,B,fun L hL he hf F hF=>?_⟩; obtain ⟨r,z,a,hr,hD,hz,hq,hA,H'⟩:= hp L hL
     obtain ⟨D,hS,hx⟩:= vaultM P (N:=N) (t:=d) H hC hT.le hr.le hD F hz; obtain ⟨δ,hδ,hδ',hZ⟩:=choose₀
     let v:= min a (δ/2); have hv:0<v:= lt_min hA (half_pos hδ)
     refine ⟨r,T,v,hr,hT,hv,?_⟩
     filter_upwards [H' v hv (min_le_left ..),terminus N D hS δ hδ hδ' hZ] with t ⟨w,hw,hP⟩ ⟨W,hW,H₁⟩
     let G:=max W (2*w); have hG:0 ≤ G:=hW.trans (le_max_left ..); let x:= 2*(Real.exp 2*t)
     have hX (c:Side)(X:EvenA c N)(V:Train 4)(Y:Sheet c)(hp:Fused X Y x r v)(h: |mass Y| ≤ T)(hv:c=F∨z ≤|mass Y|): expo G c ≤ pebble (paleF N (sunny P V c+Y)+X):=by
         obtain ⟨hh,hp'⟩:=hx c x v X V Y hp h hv; exact (earns (le_max_left ..)).trans (H₁ c _ X hp' hh hp.cocoa hp.moo (le_trans hp.work -- GrassA not LE
          (mul_le_mul_of_nonneg_left (min_le_right ..) (Nat.cast_nonneg _)))) -- check field
     refine ⟨G,hG,fun k=>?_⟩; induction k with
     | zero=> rw [pow_zero,mul_one]; exact ⟨fun X V Y hp h=> hX _ X V Y hp h (Or.inl rfl)⟩
     | succ k ih=>
          refine ⟨fun X V Y h hv=>?_⟩; let f:=F*L^(k+1); let c:=F*L^k; by_cases hz: |mass Y| ≤ z
          · let S:Flight 4 4:=⟨L,he,hf,le_rfl,le_rfl,Nat.le_add_right ..,V⟩; have hu:f.val=c.val*L.val:=by unfold f c; rw [pow_succ,← mul_assoc]; rfl
            have hh:S.L=L:=rfl; obtain ⟨Z,M,hF',hK,hR⟩:= (hP S c f (show _ from hh.symm ▸ hu) X Y (hF.trans (Nat.le_mul_of_pos_right F.val (L^k:Side).property)) hh hz h).road
            refine (rhaps hw (le_max_right ..) hu hf).trans ((mul_le_mul_of_nonneg_left (ih.per Z S.land M hF' hK) (Real.exp_pos _).le).trans hR)
          exact hX f X V Y h hv (Or.inr (le_of_not_ge hz))
end YM.QCD.Globe
