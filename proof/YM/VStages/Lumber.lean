import YM.QCD.Globe.Dome
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
variable (P:Plan j) (i:Flavor N){R A C g t:ℝ}
include i
lemma railV (hj:4≤j) (kT T:ℝ)(h:0 < kT)(hp:0<T): ∃ L₀ B:ℕ,∀ L:Side,L₀ ≤ L.val→∃ r z a:ℝ, 0<r ∧ r≤ kT ∧ 0 < z ∧ z ≤ T ∧ 0 < a ∧ ∀ v:ℝ,0<v→ v ≤ a →∀ᶠ t:ℝ in atTop,∃ W:ℝ,0 ≤ W∧ ∀ (S:Flight j j)(c f:Side)(h:f.val=c.val*S.L.val)(X:EvenA f N)(K:Sheet f), B≤ c.val → S.L=L → |mass K| ≤ z → Fused X K (2*(Real.exp 2*t)) r v → TrailS P P S h X K (2*(Real.exp 2*t)) r v T W :=by
    obtain ⟨δ,hδ,hδ',hx⟩:= choose₀
    obtain ⟨b,hb,hF⟩:= bounces P 6; obtain ⟨K,hK,H⟩:=intoA i 6
    obtain ⟨B,H'⟩:=candy P
    let R:= b; let A:ℝ:=(8*(4*b+2))⁻¹; have hA :0 < A:=by unfold A; positivity
    obtain ⟨D,hD⟩:= foldingP (k:=j) P A hA hj hj 6 (by decide)
    obtain ⟨C,hC,hP⟩:= anthem (k:=j) (j:=j) hj hj 6
    obtain ⟨L₀,hL⟩:= tackle hδ (show 0<C+1 by linarith) N
    refine ⟨max D L₀,B,fun L he=> ?_⟩
    have hD':D≤L.val:= le_trans (le_max_left ..) he; have hL':L₀≤L.val:= le_trans (le_max_right ..) he
    obtain ⟨W,hW,H₀⟩:= choiceH P j 6 L
    let V:= W+1; have hV : 1≤V:=le_add_of_nonneg_left hW
    let u:= (C+1)*cape L 0; have hu:0<u:=by unfold u; have ht:=cape_pos L 0; positivity
    obtain ⟨r,hr1,hr⟩:= ((asks hu (zero_lt_one.trans_le hV) hp h A R hA hb).and self_mem_nhdsWithin).exists
    have hr:0<r:=hr; obtain ⟨h1,h2,h3,h4,h5,h6⟩:= hr1
    let z:=min (min r T) ((A*r)/(2^6*V^2)); have hz: 0<z:= lt_min (lt_min hr hp) (div_pos (mul_pos hA hr) (by positivity)); have hz0:z≤T:=le_trans (min_le_left ..) (min_le_right ..); have hz1:z≤r:= le_trans (min_le_left ..) (min_le_left ..)
    refine ⟨r,z,δ/2,hr,h6,hz,hz0,half_pos hδ,fun v hv he=>?_⟩
    let G:=spoolM δ v; let X:=coastW L δ v; let y:=riderW (C+1) L N; have hg:0<G:=by unfold G spoolM; positivity
    have hg' : G≤1:= (div_le_one hδ).2 (by linarith)
    have hz2:2^6*(V^2*z) ≤ A*r:=by have ht : z≤((A*r)/(2^6*V^2)):= min_le_right ..; rw [le_div_iff₀ (by positivity)] at ht; linarith only [ht]
    have hY := hL L hL' v hv
    have hX:0 ≤ X:=by unfold X coastW; have hx': 0≤ Real.exp δ-1:=sub_nonneg.mpr (Real.one_le_exp hδ.le); have hu:0≤ spoolM δ v:=hg.le; positivity
    let U:=2*V; let q:=whiskey N U X; have hh : 1≤ U:=by unfold U; linarith
    let J:ℝ:= Real.exp 4*((Fintype.card (Brick.Note N):ℝ)^2*(2*U)); obtain ⟨M,hM,H_M⟩:=heft (C:=J) (by unfold J; positivity) (show 0 < δ/2 by linarith); obtain ⟨d,hd,H_d⟩:=heft (C:=K*X) (by positivity) (show 0 < A*r by positivity)
    filter_upwards [eventually_ge_atTop d,eventually_ge_atTop M] with t ht ht'
    have he':0<t:=zero_lt_one.trans_le (hd.trans ht)
    have hqy:0 ≤ q:=by unfold q whiskey; positivity [Real.log_nonneg hh]
    refine ⟨q,hqy,fun S c f h X' K' hB hh' hk hv'=>?_⟩; obtain ⟨hA',hT',hR',hg0⟩:= H₀ S _ _ h hh'; have hT := hP S _ _ h [] (by simp); rw [List.length_nil,pow_zero, mul_one, show oldDiff (proton S h) []=_ from (show _=proton S h from rfl), hh'] at hT -- dependent simp
    refine feastQ (δ:=δ) (t:=z) (A:=2*r) (r:=r) (w:=V) (v:=y) (u:=G) (η:=4*A*r) (b:=2*u) S h P P i H (hA'.up (by unfold V; linarith)) (hT'.up (by unfold V;linarith)) (hR'.up (by unfold V; linarith)) (hD S c f h (hh'.symm ▸ hD')) (Cent.up hT (show _ ≤ u from mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (cape_pos ..).le)) (hF _ c) (H' _ c hB) hv' (by positivity) hz.le hr.le hg hg' hδ hδ' hx hk (by linarith) h1 (by positivity) he' ?_ ?_ hY.1 hA.le hV (by linarith) (by positivity) ?_ ?_ hX hY.2 ?_ h4 hb ?_ h5
    · have hq:G⁻¹*v=δ/2:=by unfold G spoolM; field_simp
      rw [hq]; have ht := H_M t ht'; change (t:ℝ)⁻¹^2*_ ≤ _ at ht; unfold J U at ht; linarith
    · change 0 ≤ riderW _ _ _; unfold riderW titanic stemF Jets.Sun.fingers; unfold u at hu; positivity
    · unfold y riderW titanic u; exact le_of_eq (by ring)
    · unfold X coastW; rw [hh']
    · have hl:=Real.one_le_exp (by norm_num : 0 ≤ (2:ℝ)); have ht'' : t≤2*(2*(Real.exp 2*t)):=by nlinarith
      have he:= H_d _ (ht.trans ht''); linarith only [h3,hz2,he]
    have he0:0<8*(4*b+2):=by positivity
    change 2* dimeZ b (4*((8*(4*b+2))⁻¹)*r)≤ _; exact le_of_eq (by unfold dimeZ; field_simp; ring)

omit i
section vp
variable (P:Plan j) (i:Flavor N){a v t C T b r δ:ℝ}{L:Side}
lemma vaultD (hp:FawnP P b t T)(he:0<b)(ht:0 ≤ T)(hr:0≤r)(hv:r ≤ t)(K:Side)(ha:0 < a):∃ C:ℝ,1≤C∧∀ (c:Side)(w R:ℝ)(X:EvenA c N)(U:Train j)(M:Sheet c),Fused X M w r R → |mass M| ≤ T→ (c=K∨ a ≤ |mass M|) → let D:=sunny P U c+M; IsUnit D.det∧Beam D⁻¹ 0 C:=by
     obtain ⟨u,hh,H⟩:=maxW P hp he _ K rfl a ha; obtain ⟨x,hx,hX⟩:= bounces P 6; obtain ⟨C,hC,H'⟩:=thickV (x+T+r) u (by positivity) (zero_le_one.trans hh)
     refine ⟨C,hC,fun c w R X z M hv' hk hB=>?_⟩; obtain ⟨B,hG,hP,hQ⟩:=counting hv'.tone hv'.rateG; let F:= sunny P z c; let f:ℂ:=mass M; let d:=F+f • 1+B;
     have hs:Beam B 6 r:=by
         have hm:= hv'.remS
         nth_rw 1 [hG] at hm; rwa [add_sub_cancel_left] at hm
     obtain ⟨hf,hD⟩:=H _ B z (mass M) hQ (hs.up hv) hP hk hB
     have hY : F+M=d:=by nth_rw 1 [hG]; rw [← add_assoc]
     intro D; unfold D; rw [hY]; have hΨ:Beam d 6 (x+T+r):=((hX z c).add ((Ton.one.smul f).up (by unfold f; rw [Complex.norm_real,Real.norm_eq_abs,mul_one]; exact hk))).add hs; exact ⟨hf,H' c d hΨ hD hf⟩
structure Woo (P:Plan j)(B:Side)(N:ℕ)(t r a T W:ℝ):Prop where
 per (x:EvenA B N)(y: Train j)(K:Sheet B): Fused x K t r a→ |mass K| ≤ T→expo W B ≤ pebble (paleF N (sunny P y B+K)+x)
lemma keeperQ (hj:4≤j)(P:Plan j) (N:ℕ)(i:Flavor N):∃ L₀ B:ℕ,∀ L:Side,L₀ ≤ L.val→Odd L.val→3 ≤L.val→∀ F:Side,B≤F.val→∃ r T v:ℝ,0<r∧0 < T∧0<v ∧ ∀ᶠ t:ℝ in atTop, ∃ W:ℝ,0 ≤ W∧∀ k:ℕ, Woo P (F*L^k) N (2*(Real.exp 2*t)) r v T W:=by
     obtain ⟨C,d,T,hC,hd,hT,H⟩:= area_sol P; obtain ⟨L,B,hp⟩:= railV P i hj d T hd hT
     refine ⟨L,B,fun L hL he hf F hF=>?_⟩; obtain ⟨r,z,a,hr,hD,hz,hq,hA,H'⟩:= hp L hL
     obtain ⟨D,hS,hx⟩:= vaultD P (N:=N) (t:=d) H hC hT.le hr.le hD F hz; obtain ⟨δ,hδ,hδ',hZ⟩:=choose₀
     let v:= min a (δ/2); have hv:0<v:= lt_min hA (half_pos hδ)
     refine ⟨r,T,v,hr,hT,hv,?_⟩
     filter_upwards [H' v hv (min_le_left ..),terminus N D hS δ hδ hδ' hZ] with t ⟨w,hw,hP⟩ ⟨W,hW,H₁⟩
     let G:=max W (2*w); have hG:0 ≤ G:=hW.trans (le_max_left ..); let x:= 2*(Real.exp 2*t)
     have hX (c:Side)(X:EvenA c N)(V:Train j)(Y:Sheet c)(hp:Fused X Y x r v)(h: |mass Y| ≤ T)(hv:c=F∨z ≤|mass Y|): expo G c ≤ pebble (paleF N (sunny P V c+Y)+X):=by
         obtain ⟨hh,hp'⟩:=hx c x v X V Y hp h hv; exact (earns (le_max_left ..)).trans (H₁ c _ X hp' hh hp.cocoa hp.moo (le_trans hp.work -- GrassA not LE
          (mul_le_mul_of_nonneg_left (min_le_right ..) (Nat.cast_nonneg _)))) -- check field
     refine ⟨G,hG,fun k=>?_⟩; induction k with
     | zero=> rw [pow_zero,mul_one]; exact ⟨fun X V Y hp h=> hX _ X V Y hp h (Or.inl rfl)⟩
     | succ k ih=>
          refine ⟨fun X V Y h hv=>?_⟩; let f:=F*L^(k+1); let c:=F*L^k; by_cases hz: |mass Y| ≤ z
          · let S:Flight j j:=⟨L,he,hf,hj,le_rfl,Nat.le_add_right ..,V⟩; have hu:f.val=c.val*L.val:=by unfold f c; rw [pow_succ,← mul_assoc]; rfl
            have hh:S.L=L:=rfl; obtain ⟨Z,M,hF',hK,hR⟩:= (hP S c f (show _ from hh.symm ▸ hu) X Y (hF.trans (Nat.le_mul_of_pos_right F.val (L^k:Side).property)) hh hz h).road
            refine (rhaps hw (le_max_right ..) hu hf).trans ((mul_le_mul_of_nonneg_left (ih.per Z S.land M hF' hK) (Real.exp_pos _).le).trans hR)
          exact hX f X V Y h hv (Or.inr (le_of_not_ge hz))

end vp
section kq
variable (P:Plan j)(L B:Side)(i:Flavor N)
variable {V T t v r W d a x w:ℝ}
lemma seedsQ (K':ℕ) (c:Side) (B:ℕ) (hh:B ≤ c.val)(u:Train j)(Z: EvenA c N) (M:Sheet c)(Y:ℝ)(hp:K'=N) (hz:Cocoa Z)(h: Mercy i 6 T)(ht: GrassA Z (2*t) 6 a)(ht':a≤d)(hd:0<t)(hv:Fintype.card (Site c)>0)(hr:0 ≤r)(hf:1/2 ≤ sheen M)(hM: Tempo M)(hY:Beam M 6 V)(hV:0≤V)(hw:(2*t)⁻¹^2*T*a ≤ x)(he:0≤x)(hh':x≤1/4) (hq:2*dimeZ V x ≤r)(hy:dimeZ V x ≤ v) (hhU: M=sunny P u c) (hW: Woo P c N t r d v W):expo ((2* (Fintype.card Lat.Fiber:ℝ)*N)*Real.log 2 +a+W) c ≤ pebble (paleF N M+Z):=by
    let X:=oilD Z; let H:=feeF i X; let G:=peakZ X; have ht₀:0<2*t:=by positivity
    have h0: GrassA X (2*t) 6 a:= (cardsY Z ht ht₀).1; have hQ:= peaked Z hz; obtain ⟨w',_,hJ,hU,O,A',hk⟩:=lin G (by rw [show G=X-paleF N H from Eq.symm (by nth_rw 1 [mercyR X i (oil₀ Z) hQ.flavorG]; exact add_sub_cancel_left ..)]; exact hQ.sub ((hQ.pick i).butter _)) (Globe.forged _) ((show GrassA G (2*t) 6 d from le_trans ((cardsY X h0 ht₀).2) (mul_le_mul_of_nonneg_left ht' (Nat.cast_nonneg _)))) hd M H hM (hQ.pick i) hY ((h _ _ _ _ ht₀ hQ h0).up hw) he hV hf hh';
    let A:= dub M H w'; let F:= wearK c N w' G
    have hu: Fused F A t r d:=⟨hk.tone,hk.rateG,hk.remS.up hq,hk.cocoa,hk.moo,hk.work⟩
    let Z':= paleF N (M+A)+F; have he' : wearK c N w' (exp (paleF N M+oilD Z))=exp Z':=by apply Eq.trans _ O; congr 2; rw [Port.oneC]; rw [add_assoc]; exact congr_arg _ (mercyR X i (oil₀ Z) hQ.flavorG) -- fix
    have Hc:=mantle Z M Z' he' hJ hU ht ht₀
    have hK: expo W c ≤ pebble Z':=by unfold Z'; rw [hhU]; exact hW.per F u A hu (A'.trans hy)
    unfold expo; rw [mul_add,Real.exp_add]; exact le_trans (mul_le_mul_of_nonneg_left hK (Real.exp_pos _).le) Hc

end kq

section m
variable (P:Plan j) (i:Flavor N)
structure FreeholdQ (P:Plan j)(N:ℕ)(L:Side)(c:Side)(A : ℝ):Prop where
 port:∃ v w:ℝ,0<v ∧ 1 ≤w ∧∀ (j₀:ℕ)(B:Side)(he:B=c*L^j₀)(t:Train j)(X:EvenA B N), Cocoa X→ GrassA X w 6 v→ expo A B ≤ pebble (paleF N (sunny P t B)+X)
include i
lemma coreD (hj:4≤j): ∃ m B:ℕ,∀ (L c:Side), m≤ L.val→ Odd L.val→3 ≤ L.val→ B≤ c.val→∃ A:ℝ,0 ≤ A∧ FreeholdQ P N L c A :=by
    obtain ⟨L,B,H⟩:= keeperQ hj P N i; obtain ⟨D,hD⟩:= candy P; refine ⟨L,max D B,fun S c hL he hf hz=>?_⟩
    obtain ⟨r,T,v,hr,hT,hv,h⟩:= H S hL he hf c (le_trans (le_max_right ..) hz); obtain ⟨C,hC,hK⟩:= intoA i 6; obtain ⟨M,hM,hf⟩:= bounces P 6
    let J:=2*(4*M+2); have hJ:0<J:=by unfold J; positivity
    let d:= min (min (r/J) (T/J)) (1/4); have hp: 0 < d:=lt_min (lt_min (div_pos hr hJ) (div_pos hT hJ)) (by norm_num); have hp':d≤1/4:=min_le_right ..; have h1:2*dimeZ M d ≤ r:=by unfold dimeZ; have hh:=le_trans (min_le_left ..) (min_le_left (r/J) (T/J)) (a:=d); rw [le_div_iff₀ hJ] at hh; unfold J at hh; linarith only [hh]
    have h2:dimeZ M d ≤T:=by unfold dimeZ; have hh:=le_trans (min_le_left ..) (min_le_right (r/J) (T/J)) (a:=d); rw [le_div_iff₀ hJ] at hh; unfold J at hh; nlinarith only [hh,hT] -- edit
    obtain ⟨x,hx,Q⟩:=heft (C:=C*v) (by positivity) hp
    obtain ⟨t,hg,ht⟩:=(h.and (eventually_ge_atTop x)).exists
    obtain ⟨W,hW,hX⟩:=hg; let u:=2*(Real.exp 2*t); have hu: x ≤ u:=by unfold u; have ht:0<t:=zero_lt_one.trans_le (hx.trans ht); nlinarith [Real.one_le_exp (by norm_num : 0 ≤ (2:ℝ))]
    have hA: 1≤u:=hx.trans hu
    refine ⟨2*(Fintype.card Fiber:ℝ)*N*Real.log 2+v+W,by positivity,⟨v,2*u,hv,by linarith,fun j B he t X h ht=>?_⟩⟩
    have hpB : D≤ B.val:=he.symm ▸ ((le_trans (le_max_left ..) hz).trans (Nat.le_mul_of_pos_right c.val (S^j:Side).property))
    refine seedsQ P i N B D hpB t X (sunny P t B) 0 rfl h hK ht le_rfl (by linarith) (by positivity) hr.le (hD _ _ hpB) (savior ..) (hf ..) hM ?_ hp.le hp' h1 h2 rfl (he.symm ▸ (hX j)); rw [mul_assoc]; exact Q _ (by linarith)

end m
end YM.QCD.Globe
#print axioms YM.QCD.Globe.coreD
