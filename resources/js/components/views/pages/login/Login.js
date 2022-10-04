import React from 'react'
import {Link, Navigate} from 'react-router-dom'
import {
    CButton,
    CCard,
    CCardBody,
    CCardGroup,
    CCol,
    CContainer,
    CForm,
    CFormInput,
    CInputGroup,
    CInputGroupText,
    CRow,
} from '@coreui/react'
import CIcon from '@coreui/icons-react'
import {cilLockLocked, cilUser} from '@coreui/icons'
import axios from "axios";
import {isLoggedIn, login, walletConnect} from "../../../helpers/authHelper";
import {swalError} from "../../../helpers/common";
import {useDispatch} from "react-redux";
import fetchWrapper from "../../../helpers/fetchWrapper";

const Login = () => {

    const dispatch = useDispatch();

    const setUserToken = (user, token) => {
        dispatch({type: 'set', user: user, token: token});
        fetchWrapper.defaults.headers.common['Authorization'] = 'Bearer ' + token;
        localStorage.setItem('token', token);
    }

    const walletConnectHandler = (e) => {
        e.preventDefault();
        walletConnect().then(response => {
            if (response && response.user && response.token) {
                setUserToken(response.user, response.token);
            }
        }).catch(error => {
            swalError("Error connecting wallet");
        })
    }

    const handleSubmit = (e) => {
        e.preventDefault()
        const email = e.target.email.value;
        const password = e.target.password.value;
        login(email, password).then(response => {
                if (response && response.user && response.token) {
                    setUserToken(response.user, response.token);
                }
            }
        ).catch(error => {
                swalError("Error logging in");
            }
        );
    }

    return (
        isLoggedIn() ? <Navigate to="/" replace/> :
            <div className="bg-light min-vh-100 d-flex flex-row align-items-center">
                <CContainer>
                    <CRow className="justify-content-center align-items-center">
                        <CCol md={6}>
                            <CCardGroup>
                                <CCard className="p-4">
                                    <CCardBody>
                                        <CForm onSubmit={handleSubmit}>
                                            <h1>Login</h1>
                                            <p className="text-medium-emphasis">Sign In to your account</p>
                                            <CInputGroup className="mb-3">
                                                <CInputGroupText>
                                                    <CIcon icon={cilUser}/>
                                                </CInputGroupText>
                                                <CFormInput type="email" placeholder="Email" name="email"/>
                                            </CInputGroup>
                                            <CInputGroup className="mb-4">
                                                <CInputGroupText>
                                                    <CIcon icon={cilLockLocked}/>
                                                </CInputGroupText>
                                                <CFormInput
                                                    type="password"
                                                    placeholder="Password"
                                                    name="password"
                                                />
                                            </CInputGroup>
                                            <CRow>
                                                <CCol xs={6}>
                                                    <CButton color="primary" type="submit" className="px-4">
                                                        Login
                                                    </CButton>
                                                </CCol>
                                                <CCol xs={6} className="text-right">
                                                    <CButton color="link" className="px-0">
                                                        Forgot password?
                                                    </CButton>
                                                </CCol>
                                            </CRow>
                                        </CForm>
                                    </CCardBody>
                                </CCard>
                                {/*<CCard className="text-white bg-primary py-5" style={{ width: '44%' }}>*/}
                                {/*  <CCardBody className="text-center">*/}
                                {/*    <div>*/}
                                {/*      <h2>Sign up</h2>*/}
                                {/*      <p>*/}
                                {/*        Lorem ipsum dolor sit amet, consectetur adipisicing elit, sed do eiusmod*/}
                                {/*        tempor incididunt ut labore et dolore magna aliqua.*/}
                                {/*      </p>*/}
                                {/*      <Link to="/register">*/}
                                {/*        <CButton color="primary" className="mt-3" active tabIndex={-1}>*/}
                                {/*          Register Now!*/}
                                {/*        </CButton>*/}
                                {/*      </Link>*/}
                                {/*    </div>*/}
                                {/*  </CCardBody>*/}
                                {/*</CCard>*/}
                            </CCardGroup>
                        </CCol>
                        <CCol md={2}>
                            <div className="d-flex align-items-center">
                                <h6>OR</h6>
                                <CButton className="mx-3" onClick={walletConnectHandler}>CONNECT WALLET</CButton>
                            </div>

                        </CCol>
                    </CRow>
                </CContainer>
            </div>
    )
}

export default Login
