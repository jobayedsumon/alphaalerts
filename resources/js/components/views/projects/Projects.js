import React from 'react'
import DataTable from 'react-data-table-component';
import CustomTable from "../../common-components/CustomTable";
import {Link} from "react-router-dom";

const columns = [
    {
        name: 'Projects',
        selector: row => row.project_name,
        sortable: true,
    },
    {
        name: 'Server ID',
        selector: row => row.server_id,
        sortable: true,
    },
    {
        name: 'Channel IDs',
        selector: row => row.channel_ids,
        sortable: true,
    },
    {
        name: 'Actions',
        selector: row => <div>
            <Link to={`/projects/${row.id}/edit`} className="btn btn-primary btn-sm">
                <i className="fa fa-edit"></i>
            </Link>
            <button className="btn btn-danger btn-sm mx-2">
                <i className="fa fa-trash"></i>
            </button>
        </div>,
    },
];

const data = [
    {
        id: 1,
        project_name: 'Beetlejuice',
        server_id: '123456789',
        channel_ids: '123456789, 987654321',
    },
    {
        id: 2,
        project_name: 'Beetlejuice',
        server_id: '123456789',
        channel_ids: '123456789, 987654321',
    },
]

const Projects = () => {

    return (
        <>
            <CustomTable title="Projects" columns={columns} data={data} createLink="/projects/create" />
        </>
    )
}

export default Projects
