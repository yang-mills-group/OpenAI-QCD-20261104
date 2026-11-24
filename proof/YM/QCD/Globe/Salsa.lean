import YM.QCD.Globe.Soca
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
open Brick Nola Trees
variable (S h)(Z: EvenA f N) (X: Sheet f){a b A C δ μ χ t s w u:ℝ}
set_option quotPrecheck false
lemma cardsY (Y:EvenA c N)(he:GrassA Y t m a)(hv:0<t):GrassA (oilD Y) t m a ∧ GrassA (peakZ Y) t m a:=by
    have hf:GrassA (oilD Y) t m a:=GrassA.invert Y he (fun i=>by change ‖coef i (Y.val-(Stew.stage 0 Y).val)‖≤_; rw [map_sub,raze]; split<;> simp) hv
    refine ⟨hf,GrassA.invert Y he (fun i=> ?_) hv⟩
    change ‖coef i (Y.val-(Stew.stage 0 Y).val-(Stew.stage 2 Y).val)‖≤_; rw [map_sub,map_sub,raze,raze]; split_ifs<;>simp
lemma settler (F:Kit.Rail f c)(D:Kit.Rail c f)(i:ℕ): Stew.stage i (switchU F D Z)=switchU F D (Stew.stage i Z):=by
    apply Subtype.ext; let f:= adapter (choir N F) (choir N D)ᵀ; change panel i (f Z.val)=f (panel i Z.val); generalize Z.val=x
    rw [← write x]; simp only [map_sum,map_smul]; refine sum_congr rfl fun j _=>?_ ; rw [past _ _ (show f (mono j)∈Grass.layer _ j.card from exterior_layer _ (homogeneous j)),past _ _ (homogeneous j)]; split; · rfl
    rw [map_zero]
lemma mercyR (W:EvenA c N)(b:Flavor N)(ht: UPr W=0)(h:Fit W): W=paleF N (feeF b W) +peakZ W:=by
    have hv : paleF N (feeF b W)=Stew.stage 2 W:=by
        apply Subtype.ext; change form _ =panel 2 W.val; rw [rank_two W h, legal W h b]
    have ho:oilD W=W:=by apply Subtype.ext; change W.val-(panel 0 W.val)=_; rw [bush,show coef ∅ W.val=0 from ht]; simp
    rw [hv,peakZ,ho]; abel
lemma summationP (P:Plan j)(X:Sheet f)(ht:Tempo X)(hp:Pure Z)(hv:Cocoa Z)(hq:0<χ)(h':χ ≤ 1)(ha:0 < a)(hy:a ≤ 1)(hm:degreePriceCard (Real.exp a-1) 1 ≤1/2)(hk: Beam (father S h+X)⁻¹ m C)(hi:IsUnit (father S h+X).det)(hc: GrassA Z (2*(Real.exp 2*t)) m δ)(hA:0<t)(hH: χ⁻¹*δ+t⁻¹^2*Real.exp 4*( (Fintype.card (Brick.Note N):ℝ)^2*(2*C)) ≤ a)(hf:Cent (sliceL S h).parent id m A ((father S h+X)⁻¹*(tied S h 0 1)ᴴ))(hz:0≤A)(hw: 0≤w)(hS:w ≤ 1)(hx:0<s)(hh:stemF N*A*s ≤ t*w) : ∃ c':ℂ,∃ (L:EvenA c N), let F:=oilD L; let X':=peakZ F
      Kit.sheath 1 (choir N (tied S h 0 1)) (exp (paleF N (sunny P S.wing f+X)+Z).val)= ((father S h+X).det^N*Complex.exp c') • exp (paleF N (1-(tied S h 0 1)*(father S h+X)⁻¹*(tied S h 0 1)ᴴ) + F).val∧Cocoa F∧
      let m':=χ*(Real.exp a-1)*2; let R:= (S.L.val:ℝ)^4*2^m*m'; GrassA L s m R∧ GrassA F s m R∧ GrassA X' s m (R*w^4)∧ c'=UPr L:=by
    let K:=father S h+X; let Q:=tied S h 0 1; let A':=copies N K⁻¹; let D:= χ*(Real.exp a-1)*2; let l:= (S.L.val:ℝ)
    -- no DecidableEq
    obtain ⟨W,hW,hX⟩:= Nola.roiling (s:=Real.exp 2*t) locationP A' Z (fun i=>radiantB _ hk i N) hA hq h' rfl (GrassA.fetch Z hc hv (mul_pos (Real.exp_pos _) hA)) ha hy hm hH (hp ∅ (by simp)); let L:= warp S h X W; obtain ⟨hL,hzL⟩:= cocoa_step S h X Z P hi ht hv W hW
    have hg:GrassA W t m D:=by unfold GrassA; exact hX.trans_eq (by unfold D; rw [mul_assoc])
    have h1: GrassA L s m (l^4*2^m*D):=by
        have ht:= emerges S h P W X ht hg hf hx hA hh hw hS hz (J_l:=0) (by simp); rw [pow_zero,mul_one] at ht; exact ht
    have hp₀:peakZ (oilD L)=warp S h X (peakZ W):=by
        have he : Stew.stage 2 (oilD L)=Stew.stage 2 L:=by apply Subtype.ext; change panel _ (L.val-panel 0 L.val)=_; rw [map_sub,past 0 2 (chamber 0 _),if_neg (by decide), sub_zero]; rfl
        have hh:oilD (oilD L)=oilD L:=by apply Subtype.ext; change (oilD L).val-panel 0 (oilD L).val=_; rw [bush, show coef ∅ (oilD L).val=0 from oil₀ _,zero_smul,sub_zero]
        unfold peakZ; rw [he,hh]; unfold warp oilD; rw [map_sub,map_sub,show L=switchU (K⁻¹*Qᴴ) (Q*K⁻¹) W from rfl,settler W,settler W]
    have he:GrassA (peakZ (oilD L)) s m (l^4*2^m*D*w^4):=by rw [hp₀]; have hX:=emerges S h P (peakZ W) X ht (cardsY W hg hA).2 hf hx hA hh hw hS hz (forged W); rw [show (S.L.val:ℝ)^4*w^4*(2:ℝ)^m*D= l^4*2^m*D*w^4 from ?_] at hX; exact hX; unfold l; ring
    exact ⟨UPr L,L,hL,hzL,h1,(cardsY L h1 hx).1,he,rfl⟩
end YM.QCD.Globe
