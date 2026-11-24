import YM.Elms.Sleek
/-! # Spin rack cutoff leading test. Spins of either orientation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace PrismD
variable (H: SourceRead.TaperHol)(K:Hol su)
open QCD.Kites Beacon
-- no need S. current zero stencil all at 1.
lemma still (h:ℝ)(J:Labels.Jet su)(d:ℕ): H.flow n d ((0:ℝ) • J) h = fun _ _=>1:=by
   funext p; apply Source.SolvesLink.unique (H.solves ..); constructor
   · rfl
   intro v; rw [show H.T.connection n d ((0:ℝ) • J) h p v=0 from ?_]; swap; · unfold SourceRead.Taper.connection Source.partConnection Source.potential; simp [Labels.Taylor.value,Tensor.diagonal,Pi.smul_apply]
   simp [Gauge.mat_one]; exact hasDerivAt_const .. -- function simp
lemma glow_zero (h:ℝ)(J:Labels.Jet su)(d:ℕ) : current (c:=n) H o d ((0:ℝ) • J) h=1:=by
     funext p; unfold current views spark; rw [← focused,still]; rfl
lemma beams_idle (i:Dike)(q:Bool) : beams q n o w 1 i=Cylinder.ap n (capEdge o w) • lineT q (place (landsE n o w) i):=by
     have he:haloW n o w 1=1:=by unfold haloW; exact Pressure.one ..
     simp only [beams,stripe,he,clutch_one]; cases q <;> simp [peggle,Matrix.smul_apply,Matrix.transpose_apply,Matrix.one_apply,stripe_star,ite_smul, mul_ite]
variable (q:Bool)(i:Dike)
lemma glut (S:Stenc)(x:Cover)(h:ℝ)(hx:x∈ S)(hS:Merian.SmallT n S d)(j:Dike) (p:UV.Multi d) : Beacon.glow H.T o h (place (wrap n (x+o)) i) (place p j) = if i=j then Cylinder.ap n (x+o)*SourceRead.profile p x h else 0:=by
     unfold Beacon.glow; have hx1: offset o (wrap n (x+o))=x:=by unfold offset; rw [map_add,add_sub_cancel_right,Merian.lift_gain S _ hS hx]
     have hz: Beacon.spun H.T o (wrap n (x+o))= Cylinder.ap n (x+o):=by
          unfold spun; rw [hx1]; dsimp only; rw [show H.T.χ _=1 from ?_]; swap; · simpa only [zero_smul,add_zero] using Merian.taper_hall (χ:=H.T) S _ hS hx timeAxis 0 (by constructor <;> norm_num)
          simp
     simp only [place,Matrix.of_apply,hx1,hz]; by_cases h:i=j; · simp [h]
     split; next ht=> exact (h (Prod.ext ht.1 ht.2)).elim -- condition order
     simp_all
lemma spin_intake (S: Stenc)(V:ℝ)(J:Labels.Jet su)(hh:stop 0 w∈ S)(hS:Merian.SmallT n S d): moment H o ((0:ℝ) • J) (burnish w q i n o) V= SourceRead.desired (flora (Grass.line (twig (d:=d) q i.1 i.2 (vector (stop 0 w))))) J V:=by
    let X:=stop (0:Cover) w; let u:=twig (d:=d) q i.1 i.2 (vector X); let p:= flora (Grass.line u); let f:=Beacon.glow (c:=n) (d:=d) H.T o V; let y:=landsE n o w; let a:= Cylinder.ap n (X+o)
    rw [Beacon.moment,glow_zero]; change adapter f f (beams q n o w 1 i)= SourceRead.desired p J V; rw [beams_idle]; change adapter f f (a • lineT q (place y i))=_
    let Q:=(adapter f f)
    have h: adapter f f (lineT q (place y i))=∑ j:SpinMode d,f (place y i) j • lineT q j :=by cases q; exact adapt_psi ..; exact adapt_bar ..
    obtain ⟨F,hF⟩:=floraL (d:=d); let zBasis(h:ℝ):= observation d J h; rw [map_smul,h, placed_sum, ← observe]; unfold p u twig; rw [← hF]; simp_rw [map_sum,map_smul,Finset.smul_sum]; apply sum_congr rfl; intro b hb; rw [sum_eq_single i]
    swap; · intro k _ ht; rw [show f (place y i) (place b k)=0 from (glut (d:=d) o H i S _ V hh hS k b).trans (if_neg ht.symm), zero_smul,smul_zero]
    swap; · simp
    rw [show f (place y i) (place b i)=a*SourceRead.profile b X V from (glut (d:=d) o H i S _ V hh hS i b).trans (if_pos rfl),smul_smul,← mul_assoc a a, show a*a=1 from Pipes.ap_sq ..,one_mul,sing_scale,hF]; rw [← paced, show pace d V (flora (Grass.line (trow q b i.1 i.2)))=(V:ℂ)^spinWeight b • flora (bphy q b i.1 i.2) from Pulses.pace_slot q i.1.1 i.1.2 i.2 b V, map_smul, flora,ready_t,map_one,one_smul,timely]; rw [smul_smul,mul_comm]; rfl -- y offset casts order issue
lemma stern_prism {X:Insertion n 6}{p y:Mini d}(hp:ActionTest H o X p.val) (hY:∀ J:Labels.Jet su, SourceRead.Agrees (Beacon.moment H o ((0:ℝ) • J) X) (SourceRead.desired y.val J)):prism 0 1 d p=y:=by
    apply Subtype.ext; apply Display.unique _ _ (Submodule.coe_mem _) (Submodule.coe_mem _); intro J; have hf:= hY J; have hg:= reading o H 0 1 J hp; have he(x:Alg (Letters d)):engine 1 (Letters d) x=x:=by
         rw [←write x]; simp_rw [map_sum,map_smul, show ∀ s:Finset (Letters d), engine 1 _ (mono s)=mono s from (fun s=> by rw [nominate (mono s) 1 s.card (Grass.homogeneous s)]; simp)]
    erw [show engine _ (Letters d) ∘ (Beacon.moment H o ((0:ℝ) • J) ⇑X)=Beacon.moment H o ((0:ℝ) • J) ⇑X from funext fun _=> he _] at hg; exact ⟨hg.2.1,hf.2.1,fun i hi=>(hg.2.2 _ hi).symm.trans (hf.2.2 _ hi)⟩
include K
lemma growsBeams (d:ℕ) : Survey H (burnish w q i) 0 1 (setas d (flora (Grass.line (twig q i.1 i.2 (vector (stop 0 w)))))):=by
    have hx:= brew w q i; obtain ⟨p,hp⟩:=peony H K _ _ _ d hx
    refine ⟨hx,p,hp,?_⟩; let g:=flora (Grass.line (twig (d:=d) q i.1 i.2 (vector (stop 0 w)))); let y:=setas d g
    obtain ⟨N,hN⟩:=hp; obtain ⟨M,hM⟩:= sight {stop (0:Cover) w} d
    let n:Side:= ⟨N+M+1,by positivity⟩; let o:= (0:Cover); have he:= hN n o (by change _≤N+M+1; omega); have hS:=hM n (by change _≤N+M+1; omega)
    have h : prism 0 1 d p=y:=by
        refine stern_prism o H (X:=burnish w q i n o) he (fun J=>?_); have hx: Beacon.moment H o (d:=d) ((0:ℝ) • J) (burnish w q i n o) = SourceRead.desired g J:=funext fun v=>spin_intake o w H q i _ v J (mem_singleton_self _) hS; rw [hx]; exact PrismD.dry g J
    rw [show setas d _=y from rfl,←h]; simp_rw [pow_zero,Complex.ofReal_one,inv_one,one_smul]; exact ((lumP d p 0 1).tendsto _).mono_left nhdsWithin_le_nhds
end PrismD
end Arbor
end SparK
end YM.Massive.Elm
