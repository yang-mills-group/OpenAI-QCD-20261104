import YM.QCD.Port.Forest
import YM.Next.SCHEDULE.Resize
/-! # traced evaluator after purchase and before purchase -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Port
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Tree
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Paths Metric Extra Iteration AtomF
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {f c: Side}{A t u δ C w z σ:ℝ} {b B:ℕ} {r:Ratio c f}{X:St f} {W:ℕ→Atom su 2}
lemma since (h:Tow r (sun r) (sun r) X)(hv: ∀ V, ‖zoom w X V‖<1):Tow r (sun r) (sun r) (logs w X):=by
  refine ⟨fun p d T U ht=>?_⟩; let G:= (raise r p).haze T d; let V:= sky (raise r p) U; have hf: G∈unitary _:= trail ht
  obtain ⟨L,H⟩:=auraCL G; change lap _=aura G (lap _); rw [← H]; unfold lap; rw [L.map_tsum (log_series (hv U))]
  have hh : zoom w X V=aura G (zoom w X U):=by unfold zoom QCD.Cost.notch V; rw [h.goes p d T U ht, aura_sub, aura_one hf, aura_scale]; rfl
  rw [hh]; apply tsum_congr; intro k; rw [H]; unfold logchip; have he {Q:Sheet f}(n:ℕ) : aura G (Q^n)=aura G Q ^ n:=by
    induction n with
    | zero=>simp only [pow_zero,aura_one hf]
    | succ n ih=> rw [pow_succ,pow_succ,← ih]; unfold aura; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (star G) G,hf.1,one_mul]
  rw [aura_neg,aura_scale,he]

def probe (w:ℝ)(X:St f) (W:ℕ→Atom su 2): St f:=logs w X- robe W
lemma probeTow (h:Tow r (sun r) (sun r) X)(hv:∀ V, ‖zoom w X V‖<1) : Tow r (sun r) (sun r) (probe w X W):=by
 refine ⟨fun i p T U he=> ?_⟩; exact congr_arg₂ (·-·) ((since h hv).goes i p T U he) ((unveils W r).goes i p T U he) |>.trans (aura_sub _ _ _).symm -- args
lemma traceC {p: St f} (i : Site f)(U V: Grid f) : ((Run.cell (p U) i i).trace-(Run.cell (p V) i i).trace).re=(Run.cell (p U) i i).trace.re-(Run.cell (p V) i i).trace.re:= Complex.sub_re ..
variable {j k l:ℕ}{P: Plan j}{J:Plan k}{F:Flight j k}{e:f.val=c.val*F.L.val} {η q :ℝ}
local notation "S"=>sliceL F e
lemma freeing (h: Species F e w A t u z b X)(U:Grid f) (W:ℕ→Atom su 2):
    (∑ i:Site f,(((cell (probe w X W U) i i).trace-(cell (probe w X W 1) i i).trace)).re)=Real.log ((X U).det.re)- Real.log (X 1).det.re- Extra.Iteration.action W U:=by
    rw [h.trailed,h.trailed,← reporting]; have he:= none_to_pay (f:=f) W (by decide)
    have ht i:cell (probe w X W U) i i= cell (logs w X U) i i - cell (robe W U) i i:=rfl
    simp_rw [probe,Pi.sub_apply,he,sub_zero,show ∀ i, cell (logs w X U-robe W U) i i= _ from ht,Matrix.trace_sub,Complex.sub_re,sum_sub_distrib]; ring
lemma pieties {N M: Type*}[Fintype N][Fintype M]{p:N→Site f}{q:M→Site f} {Y:Grid f→ArrayL N M}(hp:Heritage p q t u b Y A) (h:b ≤B)(ht:0≤u) : Heritage p q t u B Y A:=by
   obtain ⟨X,Y,H⟩:=hp
   have he i j:duel Y i j u B ≤ duel Y i j u b:=sum_le_sum fun a _=> mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (YM.Next.Scheduling.cover_earns h _)) ht)) (H.crop i j a).1
   exact ⟨X,Y,H.crop,H.sells,fun i=> (sum_le_sum (fun j _=> he i j)).trans (H.spends i),fun j=> (sum_le_sum (fun i _=>he i j)).trans (H.dues j)⟩

structure Swathe (F:Flight j k)(e:f.val=c.val*F.L.val)(X:St f)(W:ℕ→Atom su 2) (J: Plan k)(w θ t r q:ℝ)(b:ℕ) where
 bath : Land f (Site c) (Site c)
 knit : Pays f (Site c) (Site c)
 arcP : Pack (sliceL F e).embed (sliceL F e).embed θ t b (dusk F e J X) r bath knit
 glow : Held (sliceL F e) (dot (sliceL F e)) (dot (sliceL F e)) bath
 germ : seed bath=bath
 walk : Land f (Site f) (Site f)
 coal : Pays f (Site f) (Site f)
 att : Pack id id θ t b (probe w X W) q walk coal
 puff : Held (sliceL F e) (sun (sliceL F e)) (sun (sliceL F e)) walk
-- from plan offerings
lemma agriculture {L:Side} (h:0 < u)(he:0<σ)(l:ℕ)(q A C : ℝ)(J:Plan k) :∃ N:ℕ,∃ δ B B':ℝ,0<δ∧0<B∧0<B'∧∀ (j i:ℕ)(c f : Side)(F:Flight j k)(e:f.val=c.val*F.L.val)(w t θ:ℝ), θ≤δ → F.L=L → N ≤ i → ∀ (X:St f), Species F e w A θ u t l X  →  Tow (sliceL F e) (sun (sliceL F e)) (sun (sliceL F e)) X  → ∀ W:ℕ → Atom su 2, Charged W σ C  →  SymmetricAtoms W  →  Nonempty (Swathe F e X W J w θ u B B' i):=by
   obtain ⟨n,d,D,hd,hD,H⟩:=quest J h.le L
   obtain ⟨Y,z,hY,hz,R,V⟩:=AtomF.robe_price he C A h.le 2
   refine ⟨max (max n R) l,min d z,D+|A|,Y+|A|,lt_min hd hz,by positivity,by positivity,fun j i c f F e w t θ hθ hL hN X hX hu W hW hp=>?_⟩
   let Q:=sliceL F e
   have hi:l ≤ i:= (le_max_right ..).trans hN; have hz:=hX.forest
   obtain ⟨Z,T,hc⟩:=((((H c f Q hL i ((le_max_left ..).trans ((le_max_left ..).trans hN)) F.land).clip (hθ.trans (min_le_left ..))).sub (pieties hX.soapt hi h.le)).mono (show D+A≤D+|A| by rw [abs_of_pos hz]))
   obtain ⟨Z,T,hR,Hc⟩:= honors hc (duskTow (J:=J) hu)
   obtain ⟨Z,T,hR,Hc,Hk⟩:= carry hR Hc (funext fun U=> duskStar (hX.crease _))
   obtain ⟨x,y,hx⟩:=(((pieties hX.clump hi h.le).sub ((V f i ((le_max_right ..).trans ((le_max_left ..).trans hN)) W hW hp).clip (hθ.trans (min_le_right ..)))).mono (show A+Y≤Y+|A| by rw [abs_of_pos hz,add_comm]))
   obtain ⟨x,y,hg,he⟩:= honors hx (probeTow hu hX.pupils); exact ⟨Z,T,hR,Hc,Hk,x,y,hg,he⟩
end YM.QCD.Port
