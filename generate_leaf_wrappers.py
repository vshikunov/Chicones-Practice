#!/usr/bin/env python3
"""Reproduce the ten lower-leaf equalities and actual-cone applications."""
import argparse
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    output = args.output or source
    output.mkdir(parents=True, exist_ok=True)
    entries = json.loads((source / 'data/lower_certificates.json').read_text())
    for i, entry in enumerate(entries):
        d = entry['rho_degree']
        suffix = 'Data' if i >= 8 else ''
        sign = '-' if i in (1, 5) else ''
        text = f"""import LeanVerification.PositiveDCompletion.UpperPolynomial{i:02d}{suffix}
import LeanVerification.PositiveDCompletion.LowerPolynomial{i:02d}Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

theorem lowerNum{i:02d}_eq_upper (a f rho : ℝ) :
    lowerNum{i:02d} a f rho={sign}upperNum{i:02d} a f rho := by
  unfold lowerNum{i:02d} upperNum{i:02d}
  unfold """ + ' '.join(f'lowerNum{i:02d}Coeff{k}' for k in range(d + 1)) + '\n'
        if i >= 3:
            text += '  unfold ' + ' '.join(f'upperNum{i:02d}Coeff{k}' for k in range(d + 1)) + '\n'
        text += '  ring\n\nend LeanVerification.PositiveDCompletion\n'
        (output / f'LowerLeafEquality{i:02d}.lean').write_text(text)
        pa, pt, p1 = [power for _, power in entry['factors']]
        text = f"""import LeanVerification.PositiveDCompletion.LowerCertificate{i:02d}
import LeanVerification.PositiveDCompletion.LowerMap{i:02d}

noncomputable section
namespace LeanVerification.PositiveDCompletion

theorem lowerNum{i:02d}_pos {{a f rho : ℝ}} (ha : 1<a) (hau : a<3)
    (hf : 1<f) (hfa : f<a) (hr : a/f<rho) (hru : rho<lowerEnvelope a f) :
    0<lowerNum{i:02d} a f rho := by
  obtain ⟨x,t,u,hx,hxu,ht,htu,hu,huu,haeq,hfeq,hreq⟩ :=
    lower_correlated_coordinates ha hau hf hfa hr hru
  subst a
  rw [hfeq,hreq]
  have hp := lowerAtom{i:02d}_pos hx hxu ht htu hu huu
  have htc : 0<1-t := by linarith
  have hxc : 0<2*x := by positivity
  have hfactor : 0<(2*x)^{pa}*t^{pt}*(1-t)^{p1} := by positivity
  have hprod := mul_pos hfactor hp
  rw [←lowerNum{i:02d}_map hx hxu ht htu] at hprod
  exact pos_of_mul_pos_right hprod
    (pow_pos (lowerRhoDen_pos (by linarith : 1<1+2*x) (by linarith : 1+2*x<3) ht htu) {d}).le

end LeanVerification.PositiveDCompletion
"""
        (output / f'LowerPositivity{i:02d}.lean').write_text(text)
    print('Emitted ten lower-leaf equalities and ten cone applications')


if __name__ == '__main__':
    main()
