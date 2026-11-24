import YM.Helio.Fin
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
variable {Γ:Silo c}{A: BankP c}{U:St c}
namespace Meridian
lemma forestry (P':Plan j)(n b:ℕ)(hσ:0≤σ){r:ℝ}(hb:CreditBeam r):∃ B:ℕ,∃ T η:ℝ,0≤T∧0<η∧η≤1 ∧∀ (c:Side)(V:Train j)(x:Axis) (p:BudgetPoint), p.power≤ n→p.order ≤ b→B ≤ p.B → p.threshold ≤η→ r*p.threshold<η/2→Deposits (totalR (wood P' (0:Site c) V) x) p σ T (T/η*p.threshold) :=by
   let δ:=2*(σ+3); have hz:0<δ:=by unfold δ; linarith
   obtain ⟨B,η,K,he,hK,H⟩:= banner P' δ hz.le -- sig
   let V:=min 1 η; have hf:0<V:=lt_min zero_lt_one he; obtain ⟨T,ht,hT⟩:= procurement B n b hb hσ; refine ⟨B,T*K,V,mul_nonneg ht (by linarith),hf,min_le_left ..,fun c Y x p hu hh hvE hθ hk=> ?_⟩
   obtain ⟨Γ,X,h,H⟩:=candor ((H c Y).clip (show V ≤ η from min_le_right ..))
   obtain ⟨-,hS⟩:=hT c x p _ V K Γ X δ h H le_rfl hvE hu hh hθ hk (min_le_left ..)
   convert hS using 1; ring
lemma polish (i n b:ℕ) (hP:0 < i)(hσ:0 ≤ σ)(ht:0<η)(P:ℝ){r:ℝ}(hX: CreditBeam r):∃ B:ℕ,∃ T ε:ℝ,0≤T∧0<ε∧ε≤1∧∀(c:Side)(V:Offer i η P)(ξ:ℝ)(x:Axis)(p: BudgetPoint),0< ξ→ ξ≤1→ p.power≤ n→p.order ≤ b→B ≤ p.B → p.threshold ≤ε*ξ→ r*p.threshold<ε*ξ/2→ Deposits (totalR (wild (Revolve.frosting V.W) ξ c) x) p σ (T*ξ) (T/ε * p.threshold):=by
    let δ:=2*(σ+3); have he:0≤δ:=by unfold δ; linarith
    obtain ⟨d,W,B,hD,hW,H⟩:= blueP i ht he
    obtain ⟨T,hT,h⟩:=procurement B n b hX hσ; let S:= min 1 d; let E:= T*W*|P|; have hp:0<S:=lt_min zero_lt_one hD
    have he':0 ≤ E:=by unfold E; positivity
    refine ⟨B,E,S,he',hp,min_le_left .., fun c V ξ x p hV hu hw hP' hf hG hn =>?_⟩
    have hQ:= H _ _ _ V.price ξ hV hu c B le_rfl; obtain ⟨Γ,Y,hM,hF⟩:= torchZ V hV hu ht (hQ.clip (show S*ξ ≤ d*ξ from mul_le_mul_of_nonneg_right (min_le_right ..) hV.le))
    obtain ⟨_,hL⟩:= h c x p _ _ _ Γ Y δ hM hF le_rfl hf hw hP' hG hn ((mul_le_of_le_one_right hp.le hu).trans (min_le_left ..))
    have hk : T*(W*P*ξ^i) ≤ E*ξ:=by
       unfold E; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self P) hW.le) (pow_nonneg hV.le _)) hT); have hl:= (pow_le_pow_of_le_one hV.le hu hP).trans_eq (pow_one ξ); nlinarith only [mul_le_mul_of_nonneg_left hl he'] -- unfold
    exact hL.thickP hk ((mul_le_mul_of_nonneg_right hk (div_nonneg p.threshold_pos.le (mul_pos hp hV).le)).trans_eq (by field_simp))
open Pressure WilsonStartup
open QCD.Kites QCD.Fork QCD.Fount QCD.Jets QCD.Raft QCD.Raft.ParcelR QCD.Jets.Touch -- check
lemma buysL (L:Side){r:ℝ}(h:CreditBeam r){κ:ℝ}(hq:0 < κ) (B:ℕ):∀ᶠ x in atTop, 0<haloK L x∧ haloK L x ≤1 ∧∀ (p:BudgetPoint),p.threshold=fiery su x L→ p.B=highR L x→ B≤p.B∧ p.threshold ≤ κ*haloK L x ∧ r*p.threshold<κ*haloK L x/2:=by
    let e:= min κ (κ/(4*r)); have hr:=h.ticket; have he:0<e:=lt_min hq (by positivity)
    filter_upwards [birthed L 1 e zero_lt_one he,(Work.E01.radiusB_tendsto.comp (Work.E09.betaF_growth su L)).eventually_ge_atTop B] with x hx hz
    obtain ⟨hm,hX,h⟩:=hx
    refine ⟨hm,hX,fun p ht hv=>?_⟩; have hu:= (pow_le_pow_of_le_one hm.le hX (show 1≤2 by norm_num)).trans_eq (pow_one _);
    rw [← ht] at h; let z:= haloK L x; have hp : p.threshold ≤ e*z:=h.trans (mul_le_mul_of_nonneg_left hu he.le); refine ⟨hv.symm ▸ hz,hp.trans (mul_le_mul_of_nonneg_right (min_le_left ..) hm.le),?_⟩
    have hk:=hp.trans (mul_le_mul_of_nonneg_right (min_le_right ..) hm.le); apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hk hr.le); change r * (κ/(4*r)*z)<κ*z/2; field_simp; linarith
structure EconomyS (P':Plan j)(L:Side)(M:ParcelR)(x:ℝ)(n b:ℕ)(σ C:ℝ):Prop where
   ready(c:Side)(V:SunR M)(Y:Train j)(z:Axis)(t:ℝ)(p:BudgetPoint):p.threshold=fiery su x L→p.B=highR L x→p.power ≤ n →p.order ≤ b→Deposits (totalR (FieldB M V c (haloK L x) P' Y + (fun (_:Grid c)=> (t • (1:Sheet c)))) z) p σ C (C*p.threshold)
lemma supervisor (P':Plan j)(M:ParcelR)(hp:M.Rates a)(n b:ℕ)(L:Side)(hσ:0≤σ): ∃ C:ℝ,0 ≤ C∧∀ᶠ x:ℝ in atTop, EconomyS P' L M x n b σ C:=by
   obtain ⟨r,hX⟩:=solvent
   obtain ⟨B,T,η,hT,hV,hA,H⟩:= forestry P' n b hσ hX
   obtain ⟨B1,S,ε,hS,hS',hθ,hY⟩:= polish 1 n b (by decide) hσ hp.hr M.c hX
   obtain ⟨B2,U,J,hU,hJ,hC,HZ⟩:= polish 2 n b (by decide) hσ hp.hs M.d hX
   let C:=T+S+U; let K:=T/η+S/ε+U/J; refine ⟨max C K,(show 0≤C by unfold C; positivity).trans (le_max_left ..),?_⟩
   filter_upwards [buysL L hX hV B, buysL L hX hS' B1, buysL L hX hJ B2] with x h1 h2 h3; obtain ⟨hx,hw,h⟩:=h1
   refine ⟨fun c V Y z t p hf hy hh he=>?_⟩; obtain ⟨hc,hB,hg⟩:= h p hf hy
   let Ξ:=haloK L x
   have hT:= H c Y z p hh he hc (hB.trans (mul_le_of_le_one_right hV.le hw)) (hg.trans_le (div_le_div_of_nonneg_right (mul_le_of_le_one_right hV.le hw) (by norm_num)))
   obtain ⟨h4,h5,h6⟩:=h2.2.2 p hf hy; obtain ⟨h7,h8,h9⟩:= h3.2.2 p hf hy
   have hs:= hY c V.X Ξ z p hx hw hh he h4 h5 h6; have hh':=HZ c V.Y Ξ z p hx hw hh he h7 h8 h9
   have heq: totalR (FieldB M V c Ξ P' Y + (fun (_:Grid c)=> t • (1:Sheet c))) z= totalR (wood P' 0 Y) z + (totalR (wild (frosting V.X.W) Ξ c) z +totalR (wild (frosting V.Y.W) Ξ c) z):=by
       let A:=fun (_:Grid c)=> t • (1:Sheet c); have he : totalR A z=0:=by ext1 U; unfold A totalR; rw [Matrix.mul_smul,Matrix.smul_mul,mul_one,one_mul,sub_self]; rfl
       rw [tplus, he, add_zero,show FieldB M V c Ξ P' Y= _+_ from (show _=wood P' 0 Y+(wild (frosting V.X.W) Ξ c+wild (frosting V.Y.W) Ξ c) from rfl), tplus,tplus]
   rw [heq]; refine (hT.duets _ (hs.duets _ hh')).thickP ?_ ?_
   · apply le_trans _ (le_max_left C K); unfold C; nlinarith only [mul_le_of_le_one_right hS hw,mul_le_of_le_one_right hU hw] -- ζ reduc
   apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right C K) p.threshold_pos.le); unfold K; ring_nf; exact le_rfl
end Meridian
end YM.QCD.Entr
#print axioms YM.QCD.Entr.Meridian.supervisor
