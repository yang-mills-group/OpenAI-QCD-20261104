import YM.Bwana.Turn
import YM.Pods.Pads
/-! Calibration inverses at ONE displaced points. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Depth.Off
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory
open Poised Plans Display Orientation Exposure Rolls Canvas
variable {S:Scheme}{r:Side}{N J d i m k:ℕ}(A:Run S N r 6)(H:SourceRead.TaperHol)(sym:RawSym) (B:Bore d)(hf:Rubric sym B) (hA:A.Actual)(W:Market S r d)(hW:Wager A H B W m)
variable (b:ℕ→ Cover)(hB:Borders S m N b)
abbrev Hora (m:ℕ)(b:ℕ→ Cover)(v w:Label d):Prop:= Tally H (b m) w (A.density m) (carrier A B b m (b m) v)
variable {v w x y:Label d}
local notation "F"=> Hora A H B m b
local notation "V₀"=> S.side r N
local notation "Sn"=> A.regulator.density
lemma horac (t:ℂ)(h:F v w): F (t • v) (t • w):=by
      unfold Hora; rw [carrier_action]; let P:=A.density m; let X:Density (S.side r m) 6:= carrier A B b m (b m) v
      have he:= Orientation.acting H (b m) d (Canvas.foil P X) w.val h.sees t
      refine ⟨h.unit,?_⟩; change Beacon.ActionTest H (b m) (Canvas.foil P (t • X)) _; rw [show Canvas.foil P (t • X)= t • Canvas.foil P X from (by funext U; simp [Canvas.foil,mul_smul_comm])]; exact he
lemma horap (h:F v w)(hp:F x y): F (v+x) (w+y):=by
      unfold Hora; rw[carrier_add]; let P:=A.density m; let X(z:Label d):Density (S.side r m) 6:= carrier A B b m (b m) z
      have he:= Orientation.actsPlus H (b m) d (Canvas.foil P (X v)) (Canvas.foil P (X x)) w.val y.val h.sees hp.sees; refine ⟨h.unit,?_⟩; change Beacon.ActionTest H (b m) (Canvas.foil P (X v+X x)) _; rw[show Canvas.foil P (X v+X x)=_ from funext fun p=> mul_add (Ring.inverse (P p)) (X v p) (X x p)]; exact he
include hB hW hA hf
lemma horas(q:Bool)(h:v≠0)(hv:moored v.val q):∃ y,y≠0 ∧ F v y:=by
      obtain ⟨y,hY,hS⟩:= ensures A H sym B hf hA W hW b hB q v h hv hW.siteM le_rfl; exact ⟨y,hY,hW.journey.furnished _ _ _ _ le_rfl hW.siteM _ (hS _)⟩
omit hB
lemma starter : F (sym.unit d) (sym.unit d):=by
      let Sn' :=AllAt A m Sn; have hu :Sn*B (S.side r N) (lup S b N m (b m)) (sym.unit d)=Sn:=by rw [hf.stone,mul_one]
      have hp:= bequeath A H sym B hf none hA W hW; have hv:Sn* draft S r B N m none (sym.unit d)=Sn:=by unfold draft Depth.visitor; change Sn* B _ _ _=_; rw[hf.stone,mul_one]
      unfold Hora carrier; rw [hu]; have hP:Fuel A H B m none (sym.unit d) (sym.unit d):= hp; unfold Fuel setS at hP; rw [hv] at hP
      have hs:= Canvas.moved H Sn' (b m) 0 hP (by rw [pier A hA hW.siteM]; exact first A _ hW.siteM _)
      rw[zero_add, first] at hs; exact hs; exact hW.siteM
lemma chora_parity (he:b m=0)(h:F x y): F (sym.parity _ x) (sym.parity _ y):=by
      have hh:Action.parity (carrier A B b m (b m) x)= carrier A B b m (b m) (sym.parity _ x):=by
          refine checkered A _ _ ?_ hW.siteM
          have hV:Action.parity Sn=Sn:=by have ht:= (arrives A N le_rfl).2.2.2.2; rw [origin] at ht; exact ht
          funext V; exact (map_mul Grass.grade ..).trans (congr_arg₂ HMul.hMul (congr_fun hV V) (congr_fun (hf.parity (S.side r N) x (lup S b N m (b m))) V))
      unfold Hora at *; rw [←hh]; have hv:Tally H 0 y (A.density m) (carrier A B b m (b m) x):=by rw [←he]; exact h
      have hc(c:Label d):= hW.reading c; let Bz:= fun x:Label d=> (⇑(B (S.side r m) 0 x):Density _ 6)
      have hY:= hingeP H (carrier A B b m (b m) x) (sym.parity _ y) Bz hv hW.reading (by rw[pier A hA hW.siteM]; exact (arrives A m hW.siteM).2.2.2.2) (hf.parity (S.side r m) y 0); nth_rw 1 [he]; exact hY
include hB
lemma bal(v:Label d):∃ y,F v y:=by
      have hg(q:Bool)(v:Label d)(h:moored v.val q):∃ y,F v y:=by
          by_cases hv:v=0; · subst v; have h:= horac A H B b (m:=m) 0 (starter A H sym B hf hA W hW b); rw[zero_smul] at h; exact ⟨_,h⟩
          obtain ⟨y,-,hp⟩:= horas A H sym B hf hA W hW b hB q hv h; exact ⟨y,hp⟩
      choose Y h using fun q=>hg q (facing sym q v) (fronting sym v q); nth_rw 1 [revelation sym v]; exact ⟨_,horap A H B b (h true) (h false)⟩
lemma cups (he:b m=0):∃ Q:Label d ≃ₗ[ℂ]Label d,(∀ x,F (Q x) x) ∧∀ v p, moored v.val p→ moored (Q v).val p:=by
      choose Y h using bal A H sym B hf hA W hW b hB
      let Z: Label d→ₗ[ℂ]Label d:={toFun:= Y,map_add':=fun x y=> Canvas.consensus _ _ _ (h _) _ (horap A H B b (h x) (h y)), map_smul':=fun c x=> Canvas.consensus _ _ _ (h _) _ (horac A H B b c (h x))}
      have hx(x): Z (sym.parity d x)=sym.parity d (Z x):= Canvas.consensus _ _ _ (h _) _ (chora_parity A H sym B hf hA W hW b he (h x))
      have hh(x):Z x=0 →x=0:=by
           intro hZ; have hp(u0:Bool)(g :Label d)(ht:moored g.val u0)(hh:Z g=0):g=0:=by
               by_contra hv; obtain ⟨y,hv,hg⟩:= horas A H sym B hf hA W hW b hB u0 hv ht; apply hv; rw [← hh]; exact Canvas.consensus _ _ _ hg _ (h g)
           have hh (q:Bool):facing sym q x=0:=by
               apply hp q _ (fronting sym x q); unfold facing; rw [map_smul]; split
               · rw [map_sub Z, hx,hZ,map_zero,show (0:Label d)-(0:Label d)=0 from sub_self (0:Label d),smul_zero]
               rw [map_add,hx,hZ,map_zero,add_zero,smul_zero]
           exact (revelation sym x).trans (by rw [hh, hh,add_zero])
      have hu:Injective Z:= fun x y he=> sub_eq_zero.mp (hh _ (by rw [map_sub Z,he,sub_self]))
      have hs:= (LinearMap.injective_iff_surjective (K:=ℂ) (V:=Label d) (f:=Z)).1 hu; let L:=LinearEquiv.ofBijective Z ⟨hu,hs⟩; let Q:=L.symm
      have hu(x:Label d): Z (Q x)= x:= L.apply_symm_apply _
      refine ⟨Q,fun x=>?_,fun v p h=> (moored_iff sym _ _).2 ?_⟩
      · nth_rw 2 [←hu x]; exact h _
      apply L.injective; change Z _= Z _; rw [hx, map_smul Z,hu]; exact (moored_iff sym _ _).1 h
omit hB hW hA hf
lemma point (y:Label d) : (fun i x=>carrier A B (fun _=>0) i x y)= trolley A (fun x=>B (S.side r N) x y) none:=by funext i x; unfold carrier trolley lup Depth.visitor; rw[zero_add,sub_zero]; rfl
include hA hf
lemma tide_here (X:Label d)(he:∀ i, i≤ J→b i=0)(hJ:J≤ N): TideT A none J (fun i x=>carrier A B b i x X):=by
      -- equal to trolley of translated stencils early only! hypothesis moves applies.
      let Fy(x:Cover):= B (S.side r N) (b N+x) X; let Y:= trolley A Fy none
      have heq(i:ℕ)(x:Cover)(h:i≤ J):carrier A B b i x X=Y i x:=by
         unfold carrier Y Fy trolley Depth.visitor lup; rw [he i h,sub_zero]; rfl
      have hT : TideT A none J Y:= wingG A hA none Fy hJ fun a c=> by unfold Fy; rw[hf.advances,add_assoc]
      refine ⟨fun i h=>⟨fun a x=> by rw[heq i x h,heq i _ h]; exact (hT.moves i h).trans a x⟩,fun i h I _ w x hp y=>?_⟩
      rw [heq i y h.le]; simp_rw [heq (i+1) _ h]; exact hT.steps i h I w x hp y
end YM.Massive.Patria.Depth.Off
#print axioms YM.Massive.Patria.Depth.Off.cups
#print axioms YM.Massive.Patria.Depth.Off.point
#print axioms YM.Massive.Patria.Depth.Off.tide_here
